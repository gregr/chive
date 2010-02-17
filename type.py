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

from storage import *

class TypeError(Exception): pass
def typeErr(ctx, msg): raise TypeError(ctx, msg)
class Type:
    def contains(self, ty): return self is ty
    def size(self): raise NotImplementedError
    def index(self, idx): raise NotImplementedError
    def unpack(self, mem, offset): raise NotImplementedError
    def pack(self, mem, offset, val): raise NotImplementedError
    def desc(self): raise NotImplementedError
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self.desc())
################################################################
# unboxed types
class UnboxedType(Type):
    def unpack(self, mem, offset): return (self, self._unpack(mem, offset))
    def _unpack(self, mem, offset): raise NotImplementedError
    def pack(self, mem, offset, val):
        tag, val = val; assert tag == self; self._pack(mem, offset, val)
    def _pack(self, mem, offset, val): raise NotImplementedError
class AtomicUnboxedType(UnboxedType):
    def size(self): return 1 # fixed size due to python
    def _unpack(self, mem, offset): return mem_read(mem, offset)
    def _pack(self, mem, offset, val): mem_write(mem, offset, val)
class ScalarType(AtomicUnboxedType):
    def __init__(self, name): self.name = name
    def desc(self): return str(self.name)
class PtrType(AtomicUnboxedType):
    def __init__(self, elt): self.elt = elt
    def contains(self, ty):
        return type(ty) is type(self) and self.elt.contains(ty.elt)
    def desc(self): return '&%s'%self.elt
class AggUnboxedType(UnboxedType):
    def _unpack(self, mem, offset): return mem_offset(mem, offset)
    def _pack(self, mem, offset, val):
        mem_copy(val, mem_offset(mem, offset), self.size())
class ArrayType(AggUnboxedType):
    def __init__(self, elt, cnt=None): self.elt = elt; self.cnt = cnt
    def contains(self, ty):
        return (type(ty) is type(self) and self.elt.contains(ty.elt)
                and (ty.cnt == self.cnt or
                    (ty.cnt is not None and ty.cnt > self.cnt))
    def size(self):
        assert self.cnt is not None; return self.cnt*self.elt.size()
    def index(self, idx): # None-length array implies dynamic extent
        assert self.cnt is None or idx>=0 and idx<self.cnt, (idx, self.desc())
        return self.elt, idx*self.elt.size()
    def desc(self):
        if self.cnt is None: pref = ''; else: pref = '%d * '%self.cnt
        return '#[%s]'%(pref+self.elt.desc())
def struct_index(struct, idx):
    assert idx>=0 and idx<len(struct.elts), (idx, struct.desc())
    return struct.elts[idx], sum(elt.size() for elt in struct.elts[:idx])
class StructType(AggUnboxedType):
    def __init__(self, elts): self.elts = elts
    def contains(self, ty):
        return (type(ty) is type(self) and
                all(t1.contains(t2) for t1, t2 in zip(self.elts, ty.elts)))
    def size(self): return sum(elt.size() for elt in self.elts)
    def index(self, idx): return struct_index(self, idx)
    def desc(self): return '#{%s}'%' '.join(lyt.desc() for lyt in self.ellyts)
################################################################
# boxed types
class BoxedType(Type):
    def size(self): return 1
    def unpack(self, mem, offset):
        node = mem_read(mem, offset); tag = node_tag(node);
        assert self.contains(tag), (tag, self); return node
    def pack(self, mem, offset, node):
        tag = node_tag(node); assert self.contains(tag), (tag, self)
        mem_write(mem, offset, node)
class AnyType(BoxedType):
    def contains(self, ty): return isinstance(ty, BoxedType)
    def desc(self): return 'Any'
anyTy = AnyType()
class NodeType(BoxedType):
    def __init__(self, name, elts): self.name = name; self.elts = elts
    def index(self, idx): return struct_index(self, idx)
    def desc(self): return str(self.name)
class UnionType(BoxedType):
    def __init__(self, elts): self.elts = elts
    def contains(self, ty):
        return (isinstance(ty, UnionType) and
                all(self.contains(elt) for elt in ty.elts))
                or any(elt.contains(ty) for elt in self.elts)
    def desc(self): return '(%s)'%'|'.join(elt.desc() for elt in self.elts)
class VarType(BoxedType):
    def __init__(self, name, constraint=anyTy):
        self.name = name; self.constraint = constraint
    def contains(self, ty): # todo: need tenv
        return (isinstance(ty, PolyType) and
                self.constraint.contains(ty.constraint))
                or self.constraint.contains(ty))
    def desc(self): return str(self.name)
class ParametricType(BoxedType):
    def __init__(self, name, params, elt):
        self.name = name; self.params = params; self.elt = elt
    def contains(self, ty): pass
    def desc(self):
        return '(%s)'%' '.join([str(self.name), ' '.join(self.params)])
