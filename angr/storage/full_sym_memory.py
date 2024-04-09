import cffi

from memory_mixins.clouseau_mixin import *
from memory_mixins.unwrapper_mixin import *
from memory_mixins.bvv_conversion_mixin import DataNormalizationMixin
from memory_mixins.name_resolution_mixin import NameResolutionMixin
from .. import sim_options as options
import paged_memory
import pitree
import claripy
import cle
from ..state_plugins.sim_action_object import _raw_ast
from ..state_plugins import SimStatePlugin

# TODO: Check for MRO?? Check seems possible only with tests
class FullSymbolicMemory(
    UnwrapperMixin,
    DataNormalizationMixin,
    InspectMixinHigh,
    NameResolutionMixin,
    SimStatePlugin
):
    def __init__(self,
                 cle_memory_backer : cle.loader.Loader =None,  # memory_backer
                 memory_id : str = None,  # kind
                 permissions_map : dict = None,  # permissions_backer
                 mapped_regions = None,  # mapped_regions
                 stack_end : int = None,  # recreate stack_range
                 stack_size : int = None,
                 timestamp : int = 0,
                 timestamp_implicit : int = 0,
                 initialized : bool = False,
                 initializable = None,
                 concrete_memory = None,
                 symbolic_memory = None,
                 **kwargs):
        if mapped_regions is None:
            mapped_regions = []
        self._memory_backer  = cle_memory_backer
        self.kind = memory_id
        self.permissions_backer = permissions_map
        self._initialized = initialized
        self._concrete_memory = paged_memory.PagedMemory(**kwargs) if concrete_memory is None else concrete_memory
        self._symbolic_memory = pitree.pitree() if symbolic_memory is None else symbolic_memory
        self._stack_end = stack_end
        self._maximum_symbolic_size = 8 * 1024
        self._maximum_concrete_size = 0x1000000
        self._stack_range = (stack_end+1-stack_size,stack_end)
        self.stack_size = stack_size
        self._mapped_regions = mapped_regions

    @property
    def timestamp(self):
        pass

    @timestamp.setter
    def timestamp(self, value):
        pass
    @property
    def implicit_timestamp(self):
        pass

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

    #     TODO: Actual init memory. No cbackers, what now??
        _ffi = cffi.FFI()



    def set_state(self,state):
        self.state = state
        self._init_memory(self)

    def _load_init_data(self, addr, size):
        page_size = 0x1000
        page_index = int(addr / page_size)
        page_end = int((addr + size) / page_size)
        # TODO: Use sorted container

    def memory_op(self, addr, size, data=None, op=None):
        addr = _raw_ast(addr)
        size = _raw_ast(size)
        data = _raw_ast(data)

        if op == 'store':
            data = self._convert_to_ast(data, size if isinstance(size, int) else None)

        reg_name = None
        if self._id == 'reg':

            if isinstance(addr,int):
                reg_name = self._reverse_addr_reg(addr)

            elif isinstance(addr,str):
                reg_addr,reg_size = super()._resolve_location_name(addr)

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
            assert type(addr) in (int, long)

        return addr, size, reg_name

    def _reverse_addr_reg(self,addr):
        for name, offset_size in self.state.arch.registers.iteritems():
            offset = offset_size[0]
            size = offset_size[1]
            if addr in range(offset, offset + size):
                return name
    def _convert_to_ast(self, thing, size, byte_width):
        super()._convert_to_ast(thing,size,byte_width)

    def get_unconstrained_bytes(self, name, bits, memory=None):
            if (memory is not None and memory.category == 'mem' and
                    options.ZERO_FILL_UNCONSTRAINED_MEMORY in self.state.options):
                return claripy.BVV(0, bits)
            state = self.state
            return state.solver.Unconstrained(name, bits)

    # TODO: Angr also does this probably, need to figure out how to inculcate it
    def build_ite(self, addr, cases, v, obj):

        assert len(cases) > 0

        if len(cases) == 1:
            cond = addr == cases[0].addr
        else:
            cond = self.state.se.And(addr >= cases[0].addr, addr <= cases[-1].addr)

        cond = claripy.And(cond, cases[0].guard) if cases[0].guard is not None else cond

        return self.state.se.If(cond, v, obj)


    # TODO: If angr does build ite, it probably also does build merged ite
    def build_merged_ite(self, addr, P, obj):

        N = len(P)
        merged_p = []
        for i in range(N):

            p = P[i]
            v = p.obj

            is_good_candidate = type(p.addr) in (int, long) and p.guard is None
            mergeable = False

            if len(merged_p) > 0 and is_good_candidate \
                    and p.addr == merged_p[-1].addr + 1:

                prev_v = merged_p[-1].obj
                if v.op == 'BVV':

                    # both constant and equal
                    if prev_v.op == 'BVV' and v.args[0] == prev_v.args[0]:
                        # if self.verbose: self.log("\tmerging ite with same constant and consecutive address")
                        mergeable = True

                # same symbolic object
                elif v is prev_v:
                    # if self.verbose: self.log("\tmerging ite with same sym and consecutive address")
                    mergeable = True

            if not mergeable:

                if len(merged_p) > 0:
                    # if self.verbose: self.log("\tbuilding ite with " + str(len(merged_p)) + " case(s)")  # " + str(addrs))
                    obj = self.build_ite(addr, merged_p, merged_p[-1].obj, obj)
                    merged_p = []

                if is_good_candidate:
                    merged_p.append(p)
                else:
                    if self.verbose:
                        self.log("\tbuilding ite with " + str(1) + " case(s)")  # " + str(addrs))
                    obj = self.build_ite(addr, [p], v, obj)

            else:
                merged_p.append(p)

        if len(merged_p) > 0:
            if self.verbose: self.log("\tbuilding ite with " + str(len(merged_p)) + " case(s)")  #: "+ str(v))
            obj = self.build_ite(addr, merged_p, merged_p[-1].obj, obj)

        return obj

    def same(self, a, b, range_a=None, range_b=None):

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
        s = FullSymbolicMemory(cle_memory_backer : cle.loader.Loader =self._memory_backer,  # memory_backer
                 memory_id : str = self._id,  # kind
                 permissions_map : dict = self._permissions_backer,  # permissions_backer
                 mapped_regions = self._mapped_regions,  # mapped_regions
                 stack_end : int = stack_end,  # recreate stack_range
                 stack_size : int = self.stack_size,
                 timestamp : int = self.timestamp,
                 timestamp_implicit : int = self.implicit_timestamp,
                 initialized : bool = False,
                 initializable = self._initializable.copy(),
                 concrete_memory = self._concrete_memory,
                 symbolic_memory = self._symbolic_memory)

        s._concrete_memory = self._concrete_memory.copy(s)

        return s
