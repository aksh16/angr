from memory_mixins.paged_memory.paged_memory_mixin import PagedMemoryMixin
import bisect


class PagedMemory(PagedMemoryMixin):
    def __init__(self, memory, pages=None, **kwargs):
        super().__init__(**kwargs)
        if pages is None:
            pages = dict()
        self._pages = pages
        self.memory = memory

    def _get_index_offset(self, addr):
        index = addr / self.PAGE_SIZE
        offset = addr % self.PAGE_SIZE
        return index, offset

    def __getitem__(self, addr):
        index, offset = self._get_index_offset(addr)
        if index not in self._pages:
            return None
        page = self._pages[index]
        if offset not in page:
            return None
        # returns the concrete pointer
        return page[offset]

    def __setitem__(self, addr, value):
        index, offset = self._get_index_offset(addr)
        if index not in self._pages:
            page = dict()
            self._pages[index] = page
        else:
            page = self._pages[index]
            page = dict(page)
            self._pages[index] = page
        page[offset] = value

    def __len__(self):
        count = 0
        for p in self._pages:
            count += len(self._pages[p])
        return count

    def find(self, start, end, result_is_flat_list=False):
        if result_is_flat_list:
            values = []
        else:
            values = {}

        range_len = end - start
        if range_len >= 1024:
            indexes = sorted(self._pages.keys())
            min_index = int(start / self.PAGE_SIZE)
            max_index = int(end / self.PAGE_SIZE)
            offset = start % self.PAGE_SIZE
            pos = bisect.bisect_left(indexes, min_index)

            while pos < len(indexes) and indexes[pos] <= max_index:
                index = indexes[pos]
                if index in self._pages:
                    page = self._pages[index]
                    while offset < self.PAGE_SIZE:
                        if offset in page:
                            if result_is_flat_list:
                                v = page[offset]
                                if type(v) in (list,):
                                    for vv in v:
                                        assert type(vv) not in (list,)
                                        values.append(vv)
                                else:
                                    values.append(v)
                            else:
                                values[index * self.PAGE_SIZE + offset] = page[offset]
                        offset += 1
                        if index * self.PAGE_SIZE + offset > end:
                            return values
                offset = 0
                pos += 1

        else:
            addr = start
            index, offset = self._get_index_offset(addr)
            while addr <= end:
                if index not in self._pages:
                    addr += self.PAGE_SIZE - offset
                    offset = 0
                    index += 1
                    continue
                if offset in self._pages[index]:
                    if result_is_flat_list:
                        v = self._pages[index][offset]
                        if type(v) in (list,):
                            for vv in v:
                                assert type(vv) not in (list,)
                                values.append(vv)
                        else:
                            values.append(v)
                    else:
                        values[addr] = self._pages[index][offset]
                addr += 1
                offset += 1
                if offset >= self.PAGE_SIZE:
                    offset = 0
                    index += 1
        return values

    def copy(self, memory):
        return PagedMemory(pages=dict(self._pages), memory=memory)

    @property
    def pages(self):
        return self._pages
