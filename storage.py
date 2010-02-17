# Copyright 2010 Gregory L. Rosenblatt

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

class Layout:
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self.desc())
    def index(self, idx): raise NotImplementedError
class ScalarLayout(Layout):
    def __init__(self, name): self.name = name
    def desc(self): return str(self.name)
    def size(self): return 1 # fixed size due to python
class StructLayout(Layout):
    def __init__(self, ellyts): self.ellyts = ellyts
    def desc(self): return '#{%s}'%' '.join(lyt.desc() for lyt in self.ellyts)
    def size(self): return sum(lyt.size() for lyt in self.ellyts)
    def index(self, idx):
        assert idx>=0 and idx<len(self.ellyts), (idx, self.desc())
        return self.ellyts[idx], sum(lyt.size() for lyt in self.ellyts[:idx])
class ArrayLayout(Layout):
    def __init__(self, ellyt, cnt): self.ellyt = ellyt; self.cnt = cnt
    def desc(self):
        if self.cnt is None: pref = ''
        else: pref = '%d * '%self.cnt
        return '#[%s]'%(pref+self.ellyt.desc())
    def size(self):
        assert self.cnt is not None; return self.cnt*self.ellyt.size()
    def index(self, idx): # None-length array implies dynamic extent
        assert self.cnt is None or idx>=0 and idx<self.cnt, (idx, self.desc())
        return self.ellyt, idx*self.ellyt.size()
def mem_alloc(sz): return (0, [None]*sz)
def mem_offset_(mem, off): return mem[0]+off
def mem_offset(mem, off): return (mem_offset_(mem, off), mem[1])
def mem_read(mem, idx): return mem[1][mem_offset_(mem, idx)]
def mem_write(mem, idx, val): mem[1][mem_offset_(mem, idx)] = val
def mem_copy(src, dst, sz):
    doff, ddat = dst; soff, sdat = src; ddat[doff:doff+sz]=sdat[soff:soff+sz]
def data_offset(mem, lyt, idx):
    lyt, off = lyt.index(idx); return lyt, mem_offset(mem, off)

if __name__=='__main__':
    ilyt = ScalarLayout('int')
    alyt = ArrayLayout(ilyt, 5)
    slyt = StructLayout((ilyt, ilyt, ilyt, alyt))
    aalyt = ArrayLayout(slyt, 4)
    dalyt = ArrayLayout(ilyt, None)

