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

################################################################
# storage
def mem_alloc(sz): return (0, [None]*sz)
def mem_realloc(mem, sz):
    off, dat = mem; dlen = len(dat); assert off == 0, (off, dat)
    if dlen > sz: dat[:] = dat[:sz]
    elif dlen < sz: dat[:] = dat+[None]*(sz-dlen)
def mem_size(mem): return len(mem[1])
def mem_offset_(mem, off): return mem[0]+off
def mem_offset(mem, off): return (mem_offset_(mem, off), mem[1])
def mem_read(mem, idx): return mem[1][mem_offset_(mem, idx)]
def mem_write(mem, idx, val): mem[1][mem_offset_(mem, idx)] = val
def mem_copy(dst, src, sz): off, dat = dst; dat[off:off+sz]=mem_toList(src, sz)
def mem_slice_get(mem, start, end):
    off, dat = mem; return (0, dat[off+start:off+end])
def mem_slice_set(dst, start, end, src):
    off, dat = dst; dat[off+start:off+end]=src[1][src[0]:]
def mem_toList(mem, sz): off, dat = mem; return dat[off:off+sz]
################################################################
# regions
class Region:
    def __init__(self): self._mutable = None; self._lifted = None
    def mutable(self):
        if self._mutable == False: typeErr(None, 'mutable(): constant region')
        self._mutable = True
    def constant(self):
        if self._mutable: typeErr(None, 'constant(): mutable region')
        self._mutable = False
    def lifted(self):
        if self._lifted == False: typeErr(None, 'lifted(): unlifted region')
        self._lifted = True
    def unlifted(self):
        if self._lifted: typeErr(None, 'unlifted(): lifted region')
        self._lifted = False
    def __str__(self):
        if self._mutable: return 'Mutable'
        elif self._mutable == False: return 'Constant'
        return 'Unknown'
################################################################
# types
class TyError(Exception): pass
def typeErr(ctx, msg): raise TyError(ctx, msg)
def isTyped(val): return (isinstance(val, list) and len(val)>0 and
                          isinstance(getTy(val), Type))
def typed(ty, val, const=None, lifted=False):
    rgn = Region(); tv = [rgn, ty, val]
    if const: rgn.constant()
    if lifted: rgn.lifted()
    else: rgn.unlifted()
    return tv
def getRgn(val): return val[0]
def getTy(val): return val[1]
def getVal(val): return val[2]
def getDiscrim(val): return getTy(val).discrim(val)
class Type:
    def contains(self, ty, tenv=None): return self is ty
    def checkTy(self, val):
        if not self.contains(getTy(val)):
            typeErr(None, "expected '%s', given '%s'"%
                    (self, getTy(val)))
    def checkIndex(self, idx, msg, exact=False):
        ni = self.numIndices()
        if ni is None and not exact: return
        if (exact and (idx != ni)) or idx<0 or idx>self.numIndices():
            typeErr(None, msg+" '%d'; %s has %d elements"% (idx, self, ni))
    def size(self): raise NotImplementedError
    def numIndices(self): return 0
    def index(self, idx): raise NotImplementedError
    def unpack(self, mem, offset): raise NotImplementedError
    def pack(self, mem, offset, val): raise NotImplementedError
    def unpackEl(self, agg, idx):
        self.checkTy(agg); elt, off = self.index(idx)
        return elt.unpack(getVal(agg), off)
    def packEl(self, agg, idx, val):
        getRgn(agg).mutable(); self.checkTy(agg)
        elt, off = self.index(idx); elt.pack(getVal(agg), off, val)
    def discrim(self, val): raise NotImplementedError
    def finiteDesc(self, seen): return [str(self)]
    def __str__(self): raise NotImplementedError
    def __repr__(self): return '<%s %s>'%(self.__class__.__name__, self)
################################################################
# unboxed types
atomicSize = 1 # fixed size due to python
class UnboxedType(Type):
    def unpack(self, mem, offs): return typed(self, self._unpack(mem, offs))
    def _unpack(self, mem, offs): raise NotImplementedError
    def pack(self, mem, offs, val):
        self.checkTy(val); self._pack(mem, offs, getVal(val))
    def _pack(self, mem, offset, val): raise NotImplementedError
class AtomicUnboxedType(UnboxedType):
    def size(self): return atomicSize
    def _unpack(self, mem, offset): return mem_read(mem, offset)
    def _pack(self, mem, offset, val): mem_write(mem, offset, val)
class ScalarType(AtomicUnboxedType):
    def __init__(self, name, pred=lambda _: True):
        self.name = name; self.pred = pred
    def new(self, val):
        if not self.pred(val):
            typeErr(None, "invalid scalar '%s'"%repr(val))
        return typed(self, val)
    def discrim(self, val): return val
    def __str__(self): return str(self.name)
class PyType(ScalarType):
    def __init__(self, name, pyty):
        super().__init__(name, (lambda x: isinstance(x, pyty)))
def cachedType(cls):
    cls._cache = {}
    def makeType(*args):
        ty = cls._cache.get(args)
        if ty is None: ty = cls(*args); cls._cache[args] = ty
        return ty
    return makeType
class PtrType(AtomicUnboxedType):
    def __init__(self, elt): self.elt = elt
    def contains(self, ty, tenv=None):
        return type(ty) is type(self) and self.elt.contains(ty.elt, tenv)
    def __str__(self): return '&%s'%self.elt
ptrType = cachedType(PtrType)
class AggUnboxedType(UnboxedType):
    def _unpack(self, mem, offset): return mem_offset(mem, offset)
    def _pack(self, mem, offset, val):
        mem_copy(mem_offset(mem, offset), val, self.size())
class UnboxedArrayType(AggUnboxedType):
    def __init__(self, elt, cnt=None): self.elt = elt; self.cnt = cnt
    def contains(self, ty, tenv=None):
        return (type(ty) is type(self) and self.elt.contains(ty.elt, tenv)
                and (ty.cnt == self.cnt or
                    (ty.cnt is not None and ty.cnt > self.cnt)))
    def size(self):
        if self.cnt is not None: return self.cnt*self.elt.size()
        else: return None
    def numIndices(self): return self.cnt
    def index(self, idx): # None-length array implies dynamic extent
        assert self.cnt is None or idx>=0 and idx<self.cnt, (idx, self)
        return self.elt, idx*self.elt.size()
    def __str__(self):
        if self.cnt is None: pref = '';
        else: pref = '%d * '%self.cnt
        return '#[%s]'%(pref+self.elt)
unboxedArrayType = cachedType(UnboxedArrayType)
def struct_index(struct, idx):
    struct.checkIndex(idx, 'invalid index')
    return struct.elts[idx], sum(elt.size() for elt in struct.elts[:idx])
class StructType(AggUnboxedType):
    def __init__(self, elts): self.elts = elts
    def contains(self, ty, tenv=None):
        return (type(ty) is type(self) and
                all(t1.contains(t2, tenv)
                    for t1, t2 in zip(self.elts, ty.elts)))
    def size(self): return sum(elt.size() for elt in self.elts())
    def numIndices(self): return len(self.elts)
    def index(self, idx): return struct_index(self, idx)
    def __str__(self): return '#{%s}'%' '.join(elt for elt in self.elts)
structType = cachedType(StructType)
################################################################
# boxed types (runtime tagging without parametric polymorphism for now)
class BoxedType(Type):
    def checkTy(self, val):
        if isinstance(getTy(val), ThunkType): return True
        super().checkTy(val)
    def size(self): return atomicSize
    def unpack(self, mem, offset):
        box = mem_read(mem, offset); self.checkTy(box); return box
    def pack(self, mem, offset, box):
        if self.checkTy(box): getVal(box).expectTy(self)
        mem_write(mem, offset, box)
class AnyType(BoxedType):
    def contains(self, ty, tenv=None): return isinstance(ty, BoxedType)
    def __str__(self): return 'Any'
anyTy = AnyType()
class VariantType(BoxedType):
    def __init__(self, elts=None):
        if elts is not None: self.init(elts)
    def init(self, elts):
        prods = []
        for elt in elts:
            if isinstance(elt, VariantType): prods.extend(elt.elts)
            else:
                assert isinstance(elt, NodeType), elt
                prods.append(elt)
        self.elts = set(prods)
    def __str__(self): return '(%s)'%'|'.join(str(elt) for elt in self.elts)
    def contains(self, ty, tenv=None):
        if isinstance(ty, VariantType):
            return all(self.contains(rhs, tenv) for rhs in ty.elts)
        else: return any(elt.contains(ty) for elt in self.elts)
class NodeType(BoxedType):
    def discrim(self, val): return getTy(val)
    def contains(self, ty, tenv=None): return ty is self
class ProductType(NodeType):
    def __init__(self, name, elts=None, fields=(), const=None):
        self.name = name; self.const = const
        if elts is not None: return self.init(elts, fields)
        self.elts = None; self.fields = {}; self.consDen = None
    def init(self, elts, fields=()):
        self.elts = elts; self.eltSize = sum(elt.size() for elt in elts)
        assert len(fields) <= len(elts), (fields, elts)
        for idx, fname in enumerate(fields):
            if fname is None: continue
            if fname in self.fields:
                typeErr(None, "type '%s' has duplicate field name: '%s'"
                              %(self.name, fname))
            self.fields[fname] = idx
    def checkValid(self):
        if self.elts is None:
            typeErr(None, "attempted to use undefined tag: '%s'"%self.name)
    def numIndices(self): self.checkValid(); return len(self.elts)
    def index(self, idx): self.checkValid(); return struct_index(self, idx)
    def fieldIndex(self, fname): return self.fields.get(fname)
    def new(self, *args):
        self.checkIndex(len(args), 'invalid number of constructor args', True)
        mem = mem_alloc(self.eltSize)
        offset = 0
        for elt, arg in zip(self.elts, args):
            elt.pack(mem, offset, arg); offset += elt.size()
        return typed(self, mem, self.const)
    def __str__(self): return str(self.name)
class ThunkType(NodeType):
    def __init__(self, name): self.name = name
    def new(self, thunk): return typed(self, thunk, lifted=True)
    def __str__(self): return '%s::thunk'%self.name
def isThunk(v): return isTyped(v) and isinstance(getTy(v), ThunkType)
class ProcType(NodeType):
    def __init__(self, inTy=None, outTy=None):
        if outTy is not None: self.init(inTy, outTy)
    def init(self, inTy, outTy): self.inTy = inTy; self.outTy = outTy
    def contains(self, ty, tenv=None):
        return (isinstance(ty, ProcType) and ty.inTy.contains(self.inTy, tenv)
                and self.outTy.contains(ty.outTy, tenv))
    def appliedTy(self, remainingApps, arity):
        ty = self; argts = []
        while remainingApps != 0 and arity != 0:
            assert isinstance(ty, ProcType), ty
            argts.append(ty.inTy); ty = ty.outTy; remainingApps-=1; arity-=1
        return ty, argts, arity
    def finiteDesc(self, seen):
        if self in seen: return ['...']
        seen.add(self); return [str(self.inTy)]+self.outTy.finiteDesc(seen)
    def __str__(self): return '(%s)'%' -> '.join(self.finiteDesc(set()))
def isProc(v): return isTyped(v) and isinstance(getTy(v), ProcType)
procType = cachedType(ProcType)
def curryProcType(paramts, rett, constr=procType):
    for paramt in reversed(paramts): rett = constr(paramt, rett)
    return rett
def uncurryProcType(ty, max=-1):
    ts = []
    while max != 0 and isinstance(ty, ProcType):
        ts.append(ty.inTy); ty = ty.outTy; max -= 1
    return ts, ty
class SpecificProcType(ProcType):
    def __init__(self, name, *args): super().__init__(*args); self.name = name
    def new(self, proc): return typed(self, proc, True)
    def __str__(self): return ('%s::%s')%(str(self.name), super().__str__())
def currySpecificProcType(name, paramts, rett):
    return curryProcType(paramts, rett,
                         (lambda *args: SpecificProcType(name, *args)))
class ArrayType(NodeType):
    def __init__(self, name, elt): self.name = name; self.elt = elt
    def checkBounds(self, ctx, arr, idx):
        cnt = arrLen(arr)
        if idx >= cnt:
            typeErr(ctx, "%s with length '%d' indexed outside bounds at '%d'"
                    %(self.name, cnt, idx))
    def index(self, idx): return self.elt, (idx*self.elt.size() + atomicSize)
    def new(self):
        arr = typed(self, mem_alloc(atomicSize)); arrSetLen(arr, 0); return arr
    def __str__(self): return str(self.name)
# todo: shrink at 1/4?
def arrElSize(arr): return getTy(arr).elt.size()
def arrIdx(arr, idx): return getTy(arr).index(idx)[1]
def arrGrow(arr, sz):
    mem = getVal(arr); mem_realloc(mem, max(sz, mem_size(mem)*2))
def arrCapacity(arr):
    return (mem_size(getVal(arr))-atomicSize)/arrElSize(arr)
def arrRequire(arr, cnt):
    if arrCapacity(arr) < cnt: arrGrow(arr, cnt*arrElSize(arr)+atomicSize)
def arrLen(arr): return mem_read(getVal(arr), 0)
def arrSetLen(arr, cnt): return mem_write(getVal(arr), 0, cnt)
def arrPush(arr, el):
    al = arrLen(arr); arrRequire(arr, al+1); getTy(arr).packEl(arr, al, el);
    arrSetLen(arr, al+1)
def arrPop(ctx, arr):
    al = arrLen(arr)
    if al < 1: typeErr(ctx, "popped empty array") # todo
    arrSetLen(arr, al-1)
#def arrConcat(arr, arg): al = arrLen(arr); return arrSlicePack(arr,al,al,arg)
def arrCheckSlice(ctx, arr, start, end):
    getTy(arr).checkBounds(ctx, arr, start-1)
    getTy(arr).checkBounds(ctx, arr, end-1)
    if start > end: typeErr(ctx, "invalid array slice: (%d,%d)"%(start, end))
def arrSliceUnpack(ctx, arr, start, end):
    arrCheckSlice(ctx, arr, start, end)
    mem = getVal(arr); start = arrIdx(arr, start); end = arrIdx(arr, end)
    return typed(getTy(arr), (0,[end-start]+mem_slice_get(mem, start, end)[1]))
def arrSlicePack(ctx, arr, start, end, arg):
    arrCheckSlice(ctx, arr, start, end)
    newLen = arrLen(arr)+arrLen(arg)-(end-start)
    mem = getVal(arr); start = arrIdx(arr, start); end = arrIdx(arr, end)
    src = mem_slice_get(getVal(arg), arrIdx(arg, 0), arrIdx(arg, arrLen(arg)))
    mem_slice_set(mem, start, end, src); arrSetLen(arr, newLen)
# do not expose
def arrToList(arr):
    return mem_toList(mem_offset(getVal(arr), atomicSize), arrLen(arr))
def arrConcatList(arr, xs):
    al = arrLen(arr); idx = arrIdx(arr, al)
    mem_slice_set(getVal(arr), idx, idx, (0, xs)); arrSetLen(arr, al+len(xs))
def isArray(v): return isTyped(v) and isinstance(getTy(v), ArrayType)
