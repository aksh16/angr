import pdb
import sys
from memory_mixins.clouseau_mixin import *
from memory_mixins.unwrapper_mixin import *
from memory_mixins.bvv_conversion_mixin import DataNormalizationMixin
from memory_mixins.name_resolution_mixin import NameResolutionMixin
from memory_mixins.paged_memory.pages import UltraPage
from .. import sim_options as options
import pitree
import claripy
import cle
from ..state_plugins.sim_action_object import _raw_ast
from ..state_plugins import SimStatePlugin, SimStateHistory, SimActionData
from ..state_plugins import inspect as stateplug_inspect
from sortedcontainers import SortedDict
from ..errors import SimSegfaultError, SimMemoryError


class MappedRegion(object):
    PROT_READ = 1
    PROT_WRITE = 2
    PROT_EXEC = 4

    def __init__(self, addr, length, permissions):
        self.addr = addr
        self.length = length
        self.permissions = permissions

    def __repr__(self):
        rwx_s = "r" if self.is_readable() else ''
        rwx_s += "w" if self.is_writable() else ''
        rwx_s += "x" if self.is_executable() else ''
        return "(" + str(hex(self.addr)) + ", " + str(hex(self.addr + self.length)) + ") [" + rwx_s + "]"

    def is_readable(self):
        return self.permissions.args[0] & MappedRegion.PROT_READ

    def is_writable(self):
        return self.permissions.args[0] & MappedRegion.PROT_WRITE

    def is_executable(self):
        return self.permissions.args[0] & MappedRegion.PROT_EXEC


class MemoryItem(object):
    __slots__ = ('addr', '_obj', 't', 'guard')

    def __init__(self, addr, obj, t, guard):
        self.addr = addr
        self._obj = obj
        self.t = t
        self.guard = guard

    @property
    def obj(self):
        if type(self._obj) in (list,):
            val = self._obj[0].bv(self._obj[1])
            self._obj = val
        return self._obj

    def __repr__(self):
        return "[" + str(self.addr) + ", " + str(self.obj) + ", " + str(self.t) + ", " + str(self.guard) + "]"

    # noinspection PyProtectedMember
    def _compare_obj(self, other):

        if id(self._obj) == id(other._obj):
            return True

        if type(self._obj) in (list,) and type(other._obj) in (list,) \
                and id(self._obj[0]) == id(other._obj[0]) \
                and self._obj[1] == self._obj[1]:
            return True

        if type(self._obj) in (list,):
            if type(self._obj[0]) not in (claripy.ast.bv.BV,):
                return False
        elif type(self._obj) not in (claripy.ast.bv.BV,):
            return False

        if type(other._obj) in (list,):
            if type(other._obj[0]) not in (claripy.ast.bv.BV,):
                return False
        elif type(other._obj) not in (claripy.ast.bv.BV,):
            return False

        a = self.obj
        b = other.obj
        if a.op == 'BVV' and b.op == 'BVV':
            return a.args[0] == b.args[0]

        return False

    def __eq__(self, other):

        if id(self) == id(other):
            return True

        if (other is None
                or self.t != other.t
                # or (type(self.addr) in (int, long) and type(other.addr) in (int, long) and self.addr != other.addr)
                or isinstance(self.obj, int) and isinstance(other.obj, int) and self.obj != other.obj
                or id(self.guard) != id(other.guard)  # conservative
                or not self._compare_obj(other)):
            return False

        return True

    def copy(self):
        return MemoryItem(self.addr, self.obj, self.t, self.guard)


# TODO: Check for MRO?? Check seems possible only with tests
class FullSymbolicMemory(
    UnwrapperMixin,
    DataNormalizationMixin,
    InspectMixinHigh,
    NameResolutionMixin,
    SimStatePlugin
):
    def __init__(self,
                 cle_memory_backer: cle.memory.Clemory = None,  # memory_backer
                 memory_id: str = None,  # kind
                 permissions_map: dict = None,  # permissions_backer
                 mapped_regions: object = None,  # mapped_regions
                 stack_end: int = None,  # recreate stack_range
                 stack_size: int = None,
                 timestamp: int = 0,
                 timestamp_implicit: int = 0,
                 initialized: bool = False,
                 initializable: object = None,
                 concrete_memory: object = None,
                 symbolic_memory: object = None,
                 **kwargs: object):
        if mapped_regions is None:
            mapped_regions = []
        self._memory_backer = cle_memory_backer
        self.kind = memory_id
        self.permissions_backer = permissions_map
        self._initializable = initializable if initializable is not None else SortedDict(key=lambda x: x[0])
        self._initialized = initialized
        self._symbolic_memory = pitree.pitree() if symbolic_memory is None else symbolic_memory
        # TODO: Need to figure what mixin to call for a pass through for ultra page
        self._concrete_memory = UltraPage(memory=self._symbolic_memory) if concrete_memory is None else concrete_memory
        self._stack_end = stack_end
        self._maximum_symbolic_size = 8 * 1024
        self._maximum_concrete_size = 0x1000000
        self._stack_range = (stack_end + 1 - stack_size, stack_end)
        self.stack_size = stack_size
        self._mapped_regions = mapped_regions
        self._initial_timestamps = [timestamp, timestamp_implicit]

    @property
    def timestamp(self):
        assert self.state is not None
        self.init_timestamps()
        return self.state.history.timestamps[0]

    @timestamp.setter
    def timestamp(self, value):
        assert self.state is not None
        self.init_timestamps()
        self.state.history.timestamps[0] = value

    @property
    def implicit_timestamp(self):
        assert self.state is not None
        self.init_timestamps()
        return self.state.history.timestamps[1]

    @implicit_timestamp.setter
    def implicit_timestamp(self, value):
        assert self.state is not None
        self.init_timestamps()
        self.state.history.timestamps[1] = value

    def init_timestamps(self):
        assert self.state is not None
        if self._initial_timestamps is not None:
            self.state.history.timestamps = self._initial_timestamps
            self._initial_timestamps = None

    @property
    def _pages(self):
        return self._concrete_memory._pages

    def _init_memory(self):
        if self._initialized:
            return

        # init map region
        for start, end in self._permissions_backer[1]:
            perms = self._permissions_backer[1][(start, end)]
            self.map_region(start, end - start, perms, internal=True)

        # Used backers inplace of cbackers. Backer is bytearray or Clemory object
        try:
            addr, data = next(self._memory_backer.backers())
            if isinstance(data, bytearray):
                data = data.decode()
            obj = claripy.BVV(data)
            page_size = 0x1000
            size = len(obj) / 8
            data_offset = 0
            page_index = int(addr / page_size)
            page_offset = addr % page_size
            while size > 0:
                max_bytes_in_page = page_index * 0x1000 + 0x1000 - addr
                mo = [page_index, obj, data_offset, page_offset, min([size, page_size, max_bytes_in_page])]
                self._initializable[page_index] = mo
                page_index += 1
                size -= page_size - page_offset
                data_offset += page_size - page_offset
                page_offset = 0

        except StopIteration:
            self._initialized = True

    def set_state(self, state):
        self.state = state
        self._init_memory()

    def _load_init_data(self, addr, size):
        page_size = 0x1000
        page_index = int(addr / page_size)
        page_end = int((addr + size) / page_size)
        k = self._initializable.bisect_left(value=page_index)

        to_remove = []
        while k < len(self._initializable) and self._initializable[k][0] <= page_end:
            data = self._initializable[k]  # [page_index, data, data_offset, page_offset, min(size, page_size]
            page = self._concrete_memory._pages[data[0]] if data[0] in self._concrete_memory._pages else None
            for j in range(data[4]):

                if page is not None and data[3] + j in page:
                    continue

                e = (data[0] * 0x1000) + data[3] + j
                v = [data[1], data[2] + j]
                self._concrete_memory[e] = MemoryItem(e, v, 0, None)

            to_remove.append(data)
            k += 1

        for e in to_remove:
            del self._initializable[e]

    def memory_op(self, addr, size, data=None, op=None):
        addr = _raw_ast(addr)
        size = _raw_ast(size)
        data = _raw_ast(data)

        if op == 'store':
            data = self._convert_to_ast(data, size if isinstance(size, int) else None, self.state.arch.byte_width)

        reg_name = None
        if self._id == 'reg':

            if isinstance(addr, int):
                reg_name = self._reverse_addr_reg(addr)

            elif isinstance(addr, str):
                reg_addr, reg_size = super()._resolve_location_name(addr)

                if size is None:
                    size = reg_size

        if size is None and type(data) in (claripy.ast.bv.BV, claripy.ast.fp.FP):
            size = len(data) // 8

        if op == 'load' and size is None:
            size = self.state.arch.bits // 8

        # TODO: Concretize size for op = load and op = store
        if size is not None:
            pass

        if type(addr) in (claripy.ast.bv.BV,) and not addr.symbolic:
            addr = addr.args[0]

        assert size is not None
        if self._id == 'reg':
            assert isinstance(addr, int)

        return addr, size, reg_name

    def _reverse_addr_reg(self, addr):
        for name, offset_size in self.state.arch.registers.iteritems():
            offset = offset_size[0]
            size = offset_size[1]
            if addr in range(offset, offset + size):
                return name

    def _convert_to_ast(self, thing, size, byte_width):
        return super()._convert_to_ast(thing, size, byte_width)

    def get_unconstrained_bytes(self, name, bits, memory=None):
        if (memory is not None and memory.category == 'mem' and
                options.ZERO_FILL_UNCONSTRAINED_MEMORY in self.state.options):
            return claripy.BVV(0, bits)
        state = self.state
        return state.solver.Unconstrained(name, bits)

    # Angr does state forking and not ite representation
    def build_ite(self, addr, cases, v, obj):

        assert len(cases) > 0

        if len(cases) == 1:
            cond = addr == cases[0].addr
        else:
            cond = self.state.se.And(addr >= cases[0].addr, addr <= cases[-1].addr)

        cond = claripy.And(cond, cases[0].guard) if cases[0].guard is not None else cond

        return self.state.se.If(cond, v, obj)

    # If we have build ite, we also need build merged ite
    def build_merged_ite(self, addr, pointer, obj):

        n = len(pointer)
        merged_p = []
        for i in range(n):

            p = pointer[i]
            v = p.obj

            is_good_candidate = type(p.addr) in int and p.guard is None
            mergeable = False

            if len(merged_p) > 0 and is_good_candidate \
                    and p.addr == merged_p[-1].addr + 1:

                prev_v = merged_p[-1].obj
                if v.op == 'BVV':

                    # both constant and equal
                    if prev_v.op == 'BVV' and v.args[0] == prev_v.args[0]:
                        mergeable = True

                # same symbolic object
                elif v is prev_v:
                    mergeable = True

            if not mergeable:

                if len(merged_p) > 0:
                    obj = self.build_ite(addr, merged_p, merged_p[-1].obj, obj)
                    merged_p = []

                if is_good_candidate:
                    merged_p.append(p)
                else:
                    obj = self.build_ite(addr, [p], v, obj)

            else:
                merged_p.append(p)

        if len(merged_p) > 0:
            obj = self.build_ite(addr, merged_p, merged_p[-1].obj, obj)

        return obj

    def same(self, a, b):

        if False and id(a) == id(b):
            return True
        try:
            cond = a != b
            return not self.state.se.satisfiable(extra_constraints=(cond,))
        except Exception as e:
            import traceback
            traceback.print_exc()
            sys.exit(1)

    def copy(self):
        s = FullSymbolicMemory(cle_memory_backer=self._memory_backer,  # memory_backer
                               memory_id=self._id,  # kind
                               permissions_map=self._permissions_backer,  # permissions_backer
                               mapped_regions=self._mapped_regions,  # mapped_regions
                               stack_end=self._stack_end,  # recreate stack_range
                               stack_size=self.stack_size,
                               timestamp=self.timestamp,
                               timestamp_implicit=self.implicit_timestamp,
                               initialized=False,
                               initializable=self._initializable.copy(),
                               concrete_memory=self._concrete_memory,
                               symbolic_memory=self._symbolic_memory)

        s._concrete_memory = self._concrete_memory.copy()

        return s

    def merge(self, others, merge_conditions, common_ancestor=None):
        assert common_ancestor is not None
        if type(common_ancestor) in (SimStateHistory,):
            ancestor_timestamp = common_ancestor.timestamps[0]
            ancestor_implicit_timestamp = common_ancestor.timestamps[1]
        else:
            ancestor_timestamp = common_ancestor.state.history.timestamps[0]
            ancestor_implicit_timestamp = common_ancestor.state.history.timestamps[1]

        assert len(merge_conditions) == 1 + len(others)
        assert len(others) == 1

        count = self._merge_concrete_memory(others[0], merge_conditions)
        count += self._merge_symbolic_memory(others[0], merge_conditions, ancestor_timestamp,
                                            ancestor_implicit_timestamp)

        self.timestamp = max(self.timestamp, others[0].timestamp) + 1
        self.implicit_timestamp = min(self.implicit_timestamp, others[0].implicit_timestamp)

        return count

    def load(self, addr, size=None, condition=None, fallback=None, add_constraints=None, action=None, endness=None,
             inspect=True, disable_actions=False, ret_on_segv=False, internal=False, ignore_endness=False):

        assert add_constraints is None

        self.state.state_counter.log.append(
            "[" + hex(self.state.regs.ip.args[0]) + "] " + "Loading " + str(size) + " bytes at " + str(addr))

        try:
            assert self._id == 'mem' or self._id == 'reg'

            if condition is not None and self.state.se.is_false(condition):
                return

            addr, size, reg_name = self.memory_op(addr, size, op='load')

            if inspect is True:
                if self.category == 'reg':
                    self.state._inspect('reg_read', stateplug_inspect.BP_BEFORE, reg_read_offset=addr,
                                        reg_read_length=size)
                    addr = self.state._inspect_getattr("reg_read_offset", addr)
                    size = self.state._inspect_getattr("reg_read_length", size)
                elif self.category == 'mem':
                    self.state._inspect('mem_read', stateplug_inspect.BP_BEFORE, mem_read_address=addr,
                                        mem_read_length=size)
                    addr = self.state._inspect_getattr("mem_read_address", addr)
                    size = self.state._inspect_getattr("mem_read_length", size)

            try:
                assert not self.state.se.symbolic(size)
            except Exception as e:
                pdb.set_trace()

            if type(size) in int:

                # concrete address
                if isinstance(addr, int):
                    min_addr = addr
                    max_addr = addr

                # symbolic addr
                else:
                    min_addr = self.state.se.min_int(addr)
                    max_addr = self.state.se.max_int(addr)
                    if min_addr == max_addr:
                        addr = min_addr

                # check permissions
                self.check_sigsegv_and_refine(addr, min_addr, max_addr, False)

                # check if binary data should be loaded into address space
                self._load_init_data(min_addr, (max_addr - min_addr) + size)

                data = None
                for k in range(size):

                    # List of memory items (symbolic pointer)
                    P = self._concrete_memory.find(min_addr + k, max_addr + k, True)

                    P += [x.data for x in self._symbolic_memory.search(min_addr + k, max_addr + k + 1)]
                    P = sorted(P, key=lambda x: (x.t, (x.addr if isinstance(x.addr, int) else 0)))

                    if min_addr == max_addr and len(P) == 1 and isinstance(P[0].addr, int) and P[0].guard is None:
                        obj = P[0].obj

                    else:

                        name = "%s_%x" % (self.id, min_addr + k)
                        obj = self.get_unconstrained_bytes(name, 8, memory=self)

                        if (self.category == 'mem' and
                                options.ZERO_FILL_UNCONSTRAINED_MEMORY not in self.state.options):
                            self.implicit_timestamp -= 1
                            self._symbolic_memory.add(min_addr + k, max_addr + k + 1,
                                                      MemoryItem(addr + k, obj, self.implicit_timestamp, None))

                        obj = self.build_merged_ite(addr + k, P, obj)

                    data = self.state.se.Concat(data, obj) if data is not None else obj

                if condition is not None:
                    assert fallback is not None
                    condition = self._raw_ast(condition)
                    fallback = self._raw_ast(fallback)
                    data = self.state.se.If(condition, data, fallback)

                # fix endness
                endness = self._endness if endness is None else endness
                if not ignore_endness and endness == "Iend_LE":
                    data = data.reversed

                if inspect is True:
                    if self.category == 'mem':
                        self.state._inspect('mem_read', stateplug_inspect.BP_AFTER, mem_read_expr=data)
                        data = self.state._inspect_getattr("mem_read_expr", data)
                    elif self.category == 'reg':
                        self.state._inspect('reg_read', stateplug_inspect.BP_AFTER, reg_read_expr=data)
                        data = self.state._inspect_getattr("reg_read_expr", data)

                if not disable_actions:
                    if options.AUTO_REFS in self.state.options and action is None and not self._abstract_backer:
                        ref_size = size * self.state.arch.byte_width if size is not None else data.size()
                        region_type = self.category
                        if region_type == 'file':
                            # Special handling for files to keep compatibility
                            # We may use some refactoring later
                            region_type = self.id
                        action = SimActionData(self.state, region_type,
                                               'write', addr=addr, data=data,
                                               size=ref_size,
                                               condition=condition)
                        self.state.history.add_action(action)

                    if action is not None:
                        action.actual_addrs = addr
                        action.actual_value = action._make_object(data)  # TODO
                        action.added_constraints = action._make_object(self.state.se.true)

                return data

            assert False

        except Exception as e:

            if type(e) in (SimSegfaultError,):
                raise e

            print(str(e))
            import traceback
            traceback.print_exc()
            sys.exit(1)

    def store(self, addr, data, size=None, condition=None, add_constraints=None, endness=None, action=None,
              inspect=True, priv=None, disable_actions=False, ignore_endness=False, internal=False):

        if not internal:
            pass

        if priv is not None:
            self.state.scratch.push_priv(priv)

        assert add_constraints is None
        condition = self._raw_ast(condition)
        condition = self.state._adjust_condition(condition)

        try:

            assert self._id == 'mem' or self._id == 'reg'

            addr, size, reg_name = self.memory_op(addr, size, data, op='store')

            if inspect is True:
                if self.category == 'reg':
                    self.state._inspect(
                        'reg_write',
                        stateplug_inspect.BP_BEFORE,
                        reg_write_offset=addr,
                        reg_write_length=size,
                        reg_write_expr=data)
                    addr = self.state._inspect_getattr('reg_write_offset', addr)
                    size = self.state._inspect_getattr('reg_write_length', size)
                    data = self.state._inspect_getattr('reg_write_expr', data)
                elif self.category == 'mem':
                    self.state._inspect(
                        'mem_write',
                        stateplug_inspect.BP_BEFORE,
                        mem_write_address=addr,
                        mem_write_length=size,
                        mem_write_expr=data,
                    )
                    addr = self.state._inspect_getattr('mem_write_address', addr)
                    size = self.state._inspect_getattr('mem_write_length', size)
                    data = self.state._inspect_getattr('mem_write_expr', data)

            if condition is not None:
                if self.state.se.is_true(condition):
                    condition = None
                elif self.state.se.is_false(condition):
                    if priv is not None:
                        self.state.scratch.pop_priv()
                    return

            # store with conditional size
            conditional_size = None
            if self.state.se.symbolic(size):
                conditional_size = [self.state.se.min_int(size), self.state.se.max_int(size)]
                self.state.se.add(self.state.se.ULE(size, conditional_size[1]))

            # convert data to BVV if concrete
            data = self._convert_to_ast(data, size if isinstance(size, int) else None,
                                        self.state.arch.byte_width)

            if isinstance(size, int) or conditional_size is not None:

                assert len(data) / 8 == (size if isinstance(size, int) else conditional_size[1])

                # simplify
                data = self.state.se.simplify(data)

                # fix endness
                endness = self._endness if endness is None else endness
                if not ignore_endness and endness == "Iend_LE":
                    if not internal:
                        pass
                    data = data.reversed

                # concrete address
                if isinstance(addr, int):
                    min_addr = addr
                    max_addr = addr

                # symbolic addr
                else:
                    min_addr = self.state.se.min_int(addr)
                    max_addr = self.state.se.max_int(addr)
                    if min_addr == max_addr:
                        addr = min_addr

                # check permissions
                self.check_sigsegv_and_refine(addr, min_addr, max_addr, True)

                self.timestamp += 1

                initial_condition = condition

                compilation_flag = 0

                for k in range(size if isinstance(size, int) else conditional_size[1]):

                    compilation_flag += 1

                    obj = [data, k]
                    if isinstance(size, int) and size == 1:
                        obj = data

                    if conditional_size is not None and k + 1 >= conditional_size[0]:
                        assert k + 1 <= conditional_size[1]
                        condition = self.state.se.UGT(size, k) if initial_condition is None else claripy.And(
                            initial_condition, self.state.se.UGT(size, k + 1))

                    inserted = False
                    constant_addr = min_addr == max_addr

                    if constant_addr:

                        assert addr == min_addr
                        # This is a tuple and not a page
                        P = self._concrete_memory[min_addr + k]
                        if P is None or condition is None:
                            self._concrete_memory[min_addr + k] = MemoryItem(min_addr + k, obj, self.timestamp,
                                                                             condition)

                        else:
                            item = MemoryItem(min_addr + k, obj, self.timestamp, condition)
                            if type(P) in (list,):
                                P = [item] + P
                            else:
                                P = [item, P]
                            self._concrete_memory[min_addr + k] = P

                        inserted = True

                    if not inserted:

                        if condition is None:

                            P = self._symbolic_memory.search(min_addr + k, max_addr + k + 1)
                            for p in P:
                                if id(p.data.addr) == id(addr + k):  # this check is pretty useless...
                                    self._symbolic_memory.update_item(p,
                                                                      MemoryItem(addr + k, obj, self.timestamp, None))
                                    inserted = True
                                    break

                    if not inserted:
                        self._symbolic_memory.add(min_addr + k, max_addr + k + 1,
                                                  MemoryItem(addr + k, obj, self.timestamp, condition))

                if inspect is True:
                    if self.category == 'reg':
                        self.state._inspect('reg_write', stateplug_inspect.BP_AFTER)
                    if self.category == 'mem':
                        self.state._inspect('mem_write', stateplug_inspect.BP_AFTER)

                if not disable_actions:
                    if options.AUTO_REFS in self.state.options and action is None and not self._abstract_backer:
                        ref_size = size * self.state.arch.byte_width if size is not None else data.size()
                        region_type = self.category
                        if region_type == 'file':
                            # Special handling for files to keep compatibility
                            # We may use some refactoring later
                            region_type = self.id
                        action = SimActionData(self.state, region_type, 'write', addr=addr,
                                               data=data,
                                               size=ref_size,
                                               condition=condition
                                               )
                        self.state.history.add_action(action)

                    if action is not None:
                        action.actual_addrs = addr
                        action.actual_value = action._make_object(data)
                        action.added_constraints = action._make_object(self.state.se.true)

                if priv is not None:
                    self.state.scratch.pop_priv()
                return

            assert False

        except Exception as e:

            if type(e) in (SimSegfaultError,):
                raise e

            import traceback
            print(str(e))
            traceback.print_exc()
            sys.exit(1)

    @property
    def category(self):
        return self._id

    @property
    def id(self):
        return self._id

    def map_region(self, addr, length, permissions):
        if hasattr(self.state, 'state_counter'):
            self.state.state_counter.log.append("[" + hex(self.state.regs.ip.args[0]) + "] " + "Map Region")

        if self.state.se.symbolic(addr) or self.state.se.symbolic(length):
            assert False

        # make if concrete
        if isinstance(addr, claripy.ast.bv.BV):
            addr = self.state.se.max_int(addr)

        # make perms a bitvector to easily check them
        if isinstance(permissions, int):
            permissions = claripy.BVV(permissions, 3)

        # keep track of this region
        self._mapped_regions.append(MappedRegion(addr, length, permissions))

        # sort mapped regions
        self._mapped_regions = sorted(self._mapped_regions, key=lambda x: x.addr)

    def permissions(self, addr):

        if self.state.se.symbolic(addr):
            assert False

        if isinstance(addr, claripy.ast.bv.BV):
            addr = self.state.se.eval(addr)

        for region in self._mapped_regions:
            if region.addr <= addr <= region.addr + region.length:
                return region.permissions

        raise SimMemoryError("page does not exist at given address")

    def check_sigsegv_and_refine(self, addr, min_addr, max_addr, write_access):

        if options.STRICT_PAGE_ACCESS not in self.state.options:
            return

        try:

            access_type = "write" if write_access else "read"

            if len(self._mapped_regions) == 0:
                raise SimSegfaultError(min_addr, "Invalid " + access_type + " access: [" + str(
                    hex(min_addr)) + ", " + str(hex(max_addr)) + "]")

            last_covered_addr = min_addr - 1
            for region in self._mapped_regions:

                # region is after our range addr
                if max_addr < region.addr:
                    break

                # region is before our range addr
                if last_covered_addr + 1 > region.addr + region.length:
                    continue

                # there is one addr in our range that could be not covered by any region
                if last_covered_addr + 1 < region.addr:

                    # check with the solver: is there a solution for addr?
                    if self.state.se.satisfiable(
                            extra_constraints=(addr >= last_covered_addr + 1, addr < region.addr,)):
                        raise SimSegfaultError(last_covered_addr + 1,
                                               "Invalid " + access_type + " access: [" + str(
                                                   hex(min_addr)) + ", " + str(hex(max_addr)) + "]")

                # last_covered_addr + 1 is inside this region
                # let's check for permissions

                upper_addr = min(region.addr + region.length, max_addr)
                if access_type == 'write':
                    if not region.is_writable() and self.state.se.satisfiable(
                            extra_constraints=(addr >= last_covered_addr + 1, addr <= upper_addr,)):
                        raise SimSegfaultError(last_covered_addr + 1,
                                               "Invalid " + access_type + " access: [" + str(
                                                   hex(min_addr)) + ", " + str(hex(max_addr)) + "]")

                elif access_type == 'read':
                    if not region.is_readable() and self.state.se.satisfiable(
                            extra_constraints=(addr >= last_covered_addr + 1, addr <= upper_addr,)):
                        raise SimSegfaultError(last_covered_addr + 1,
                                               "Invalid " + access_type + " access: [" + str(
                                                   hex(min_addr)) + ", " + str(hex(max_addr)) + "]")

                if max_addr > region.addr + region.length:
                    last_covered_addr = region.addr + region.length
                else:
                    last_covered_addr = max_addr

            # last region could not cover up to max_addr
            if last_covered_addr < max_addr:
                # we do not need to check with the solver since max_addr is already a valid solution for addr
                raise SimSegfaultError(last_covered_addr + 1, "Invalid " + access_type + " access: [" + str(
                    hex(min_addr)) + ", " + str(hex(max_addr)) + "]")

        except Exception as e:
            raise e

    def _merge_concrete_memory(self, other, merge_conditions):
        try:
            assert self._stack_range == other._stack_range

            missing_self = set(self._initializable.keys()) - set(other._initializable.keys())
            for index in missing_self:
                self._load_init_data(index * 0x1000, 1)

            assert len(set(self._initializable.keys()) - set(other._initializable.keys())) == 0

            missing_other = set(other._initializable.keys()) - set(self._initializable.keys())
            for index in missing_other:
                other._load_init_data(index * 0x1000, 1)

            assert len(set(other._initializable.keys()) - set(self._initializable.keys())) == 0

            count = 0

            page_indexes = set(self._concrete_memory._pages.keys())
            page_indexes |= set(other._concrete_memory._pages.keys())

            # assert len(page_indexes) == 0

            for page_index in page_indexes:

                # print "merging next page..."

                page_self = self._concrete_memory._pages[
                    page_index] if page_index in self._concrete_memory._pages else None
                page_other = other._concrete_memory._pages[
                    page_index] if page_index in other._concrete_memory._pages else None

                # shared page? if yes, do no touch it
                if id(page_self) == id(page_other):
                    continue

                offsets = set(page_self.keys()) if page_self is not None else set()
                offsets |= set(page_other.keys()) if page_other is not None else set()

                for offset in offsets:

                    v_self = page_self[offset] if page_self is not None and offset in page_self else None
                    v_other = page_other[offset] if page_other is not None and offset in page_other else None

                    if type(v_self) not in (list,) and type(v_other) not in (list,):

                        if v_self is not None and v_other is not None:
                            assert v_self.addr == v_other.addr
                            pass

                        same_value = v_self == v_other
                    else:
                        if type(v_self) is not type(v_other):
                            same_value = False
                        elif len(v_self) is not len(v_other):
                            same_value = False
                        else:
                            same_value = True
                            for k in range(len(v_self)):  # we only get equality when items are in the same order

                                sub_v_self = v_self[k]
                                sub_v_other = v_other[k]

                                assert type(sub_v_self) not in (list,)
                                assert type(sub_v_other) not in (list,)
                                assert sub_v_self.addr == sub_v_other.addr

                                if sub_v_self != sub_v_other:
                                    same_value = False
                                    break

                    # self has an initialized value that is missing in other
                    # we can keep as it is.
                    if v_other is None and v_self is not None and type(v_self) is not (
                            list,) and v_self.t == 0 and v_self.guard is None:
                        same_value = True

                    # Symmetric case. We need to insert in self.
                    if v_self is None and v_other is not None and type(v_other) is not (
                            list,) and v_other.t == 0 and v_other.guard is None:
                        self._concrete_memory[page_index * 0x1000 + offset] = v_other
                        same_value = True

                    if page_index * 0x1000 + offset == 134561792:
                        # pdb.set_trace()
                        pass

                    if not same_value:
                        count += 1
                        merged_value = self._copy_symbolic_items_and_apply_guard(v_self, merge_conditions[
                            0]) + self._copy_symbolic_items_and_apply_guard(v_other, merge_conditions[1])
                        assert len(merged_value) > 0
                        self._concrete_memory[page_index * 0x1000 + offset] = merged_value if len(merged_value) > 1 else \
                            merged_value[0]

            return count

        except Exception as e:
            pdb.set_trace()

    def _copy_symbolic_items_and_apply_guard(self, L, guard):
        if L is None:
            return []
        if type(L) not in (list,):
            L = [L]
        LL = []
        for l in L:
            l = l.copy()
            l.guard = claripy.And(l.guard, guard) if l.guard is not None else guard
            LL.append(l)
        return LL

    def _merge_symbolic_memory(self, other, merge_conditions, ancestor_timestamp, ancestor_timestamp_implicit,
                               verbose=False):
        try:
            count = 0
            pointer = self._symbolic_memory.search(0, sys.maxsize * 2 + 1)
            for p in pointer:
                # assert p.data.t >= 0
                if (p.data.t > 0 and p.data.t >= ancestor_timestamp) or (
                        p.data.t < 0 and p.data.t <= ancestor_timestamp_implicit):
                    guard = claripy.And(p.data.guard, merge_conditions[0]) if p.data.guard is not None else \
                        merge_conditions[0]
                    i = MemoryItem(p.data.addr, p.data.obj, p.data.t, guard)
                    self._symbolic_memory.update_item(p, i)
                    count += 1
        except Exception as e:
            error = 1
            pdb.set_trace()

        try:
            pointer = other._symbolic_memory.search(0, sys.maxsize * 2 + 1)
            for p in pointer:
                # assert p.data.t >= 0
                if (p.data.t > 0 and p.data.t >= ancestor_timestamp) or (
                        p.data.t < 0 and p.data.t <= ancestor_timestamp_implicit):
                    guard = claripy.And(p.data.guard, merge_conditions[1]) if p.data.guard is not None else \
                        merge_conditions[1]
                    i = MemoryItem(p.data.addr, p.data.obj, p.data.t, guard)
                    self._symbolic_memory.add(p.begin, p.end, i)
                    count += 1
        except Exception as e:
            pdb.set_trace()

        return count
