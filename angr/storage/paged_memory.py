from memory_mixins.paged_memory.paged_memory_mixin import PagedMemoryMixin


class PagedMemory(PagedMemoryMixin):
    def __init__(self, pages : dict = dict(), **kwargs):
        super().__init__(**kwargs)
        self._pages = pages
        self._cowed = set()




