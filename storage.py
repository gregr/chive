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
class ScalarLayout(Layout):
    def __init__(self, primValTag): self.tag = primValTag
    def desc(self): return str(self.tag)
    def size(self): return 1 # fixed size due to python
class TupleLayout(Layout):
    def __init__(self, ellyts): self.ellyts = ellyts
    def desc(self): return '#{%s}'%' '.join(lyt.desc() for lyt in self.ellyts)
    def size(self): return sum(lyt.size() for lyt in self.ellyts)
    def offset(self, n):
        assert n<len(self.elts)
        return sum(lyt.size() for lyt in self.ellyts[:n])
class ArrayLayout(Layout):
    def __init__(self, ellyt, num): self.ellyt = ellyt; self.num = num
    def desc(self):
        if self.num is None: pref = ''
        else: pref = '%d * '%self.num
        return '#[%s]'%(pref+self.ellyt.desc())
    def size(self): return self.num*self.ellyt.size()
    def offset(self, n): # None-length array implies dynamic extent
        assert self.num is None or n<self.num, n; return n*self.ellyt.size()
def mem_alloc(lyt): return (0, [None]*lyt.size())
def mem_offset(mem, off):
    off = mem[0]+off; assert off < len(mem[1]), (off, len(mem[1])
    return (off, mem[1])
def mem_deref(mem): return mem[1][mem[0]]

