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
from sortedcontainers import SortedList
from ..errors import SimSegfaultError


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
        self._initializable = initializable if initializable is not None else SortedList(key=lambda x: x[0])
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
                self._initializable.add(mo)
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
            self._initializable.remove(e)

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
    def build_merged_ite(self, addr, P, obj):

        N = len(P)
        merged_p = []
        for i in range(N):

            p = P[i]
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
                import pdb
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

                            # implicit store...
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

                if not disable_actions and self.angr_memory is None:
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
