from memory_mixins.clouseau_mixin import *
from memory_mixins.unwrapper_mixin import *
from memory_mixins.bvv_conversion_mixin import DataNormalizationMixin
from .. import sim_options as options
import paged_memory
import pitree
import claripy
import cle

class FullSymbolicMemory(
    UnwrapperMixin,
    DataNormalizationMixin,
    InspectMixinHigh
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

        self._maximum_symbolic_size = 8 * 1024
        self._maximum_concrete_size = 0x1000000
        self._stack_range = (stack_end+1-stack_size,stack_end)
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

    #     TODO: Actual init memory

    def set_state(self,state):
        self.state = state
        self._init_memory(self)

    def get_unconstrained_bytes(self, name, bits, memory=None):
            if (memory is not None and memory.category == 'mem' and
                    options.ZERO_FILL_UNCONSTRAINED_MEMORY in self.state.options):
                return claripy.BVV(0, bits)
            state = self.state
    return state.solver.Unconstrained(name, bits)
