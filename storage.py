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

def mem_alloc(sz): return (0, [None]*sz)
def mem_offset_(mem, off): return mem[0]+off
def mem_offset(mem, off): return (mem_offset_(mem, off), mem[1])
def mem_read(mem, idx): return mem[1][mem_offset_(mem, idx)]
def mem_write(mem, idx, val): mem[1][mem_offset_(mem, idx)] = val
def mem_copy(src, dst, sz):
    doff, ddat = dst; soff, sdat = src; ddat[doff:doff+sz]=sdat[soff:soff+sz]
def data_offset(mem, ty, idx):
    ty, off = ty.index(idx); return ty, mem_offset(mem, off)
