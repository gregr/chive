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
# utilities
from functools import reduce
from itertools import chain
from collections import namedtuple
class Repr:
    def __str__(self): return ''
    def __repr__(self):
        lab = self._label(); body = str(self)
        if lab: body = ' '.join((lab, body))
        return '<%s>'%body
    def _label(self): return self.__class__.__name__
divLen = 64; thickDiv = '='*divLen; thinDiv = '-'*divLen
def printDiv(msg): print(thickDiv+'\n= '+msg+'\n'+thickDiv)
def zip2(xs):
    ys = tuple(zip(*xs))
    if not ys: ys = ((), ())
    return ys
def unionReduce(xs): return reduce(set.union, xs, set())
def dictInsert(d1, kvs, combine):
    nd = d1.copy()
    for key, val in kvs:
        val1 = d1.get(key)
        if val1 is not None: val = combine(key, val1, val)
        if val is not None: nd[key] = val
        else: del nd[key]
    return nd
def dictJoin(d1, d2, combine): return dictInsert(d1, d2.items(), combine)
def alphaGen(alphabet=[chr(o) for o in range(ord('a'), ord('z')+1)]):
    count = 0
    while True:
        countStr = str(count)
        for s in alphabet: yield s+countStr
        count += 1
class UIDGen:
    def __init__(self): self.counter = 0; self.recycled = set()
    def get(self):
        if self.recycled: uid = self.recycled.pop()
        else: uid = self.counter; self.counter += 1
        return uid
    def put(self, uid):
        assert uid < self.counter, (uid, self.counter)
        self.recycled.add(uid); prev = self.counter-1
        while prev in self.recycled: self.recycled.remove(prev); prev -= 1
        self.counter = prev+1
def Label(uidg=UIDGen()): return uidg.get()
_Name = namedtuple('Name', 'str uid')
def Name(str, uidg=UIDGen()): return _Name(str, uidg.get())
_showUID = False
def strName(self):
    global _showUID
    if _showUID: return str((self.str, self.uid))
    return str(self.str)
_Name.__str__ = strName
def strTup(tup): return '(%s)'%' '.join(str(el) for el in tup)
def strDict(dct, joiner=' '):
    return '{%s}'%joiner.join('(%s => %s)'%(key, strSet(val))
                              for key, val in dct.items())
def strSet(st):
    if isinstance(st, set): return '#{%s}'%' '.join(str(el) for el in st)
    return str(st)
class Mapping(Repr):
    _combine = staticmethod(lambda _, __, val: val)
    def __init__(self, dat=None):
        if dat is None: dat = {}
        self.data = dat
    def __str__(self): return strDict(self.data)
    def _getDefault(self): return None
    def single(self, val): return val
    def get(self, key):
        val = self.data.get(key)
        if val is None: return self._getDefault()
        return val
    def insert(self, kvs):
        return self.__class__(dictInsert(self.data, kvs, self._combine))
    def join(self, other): return self.insert(other.data.items())
    def only(self, keys):
        dat = dict((key, val) for key, val in self.data.items() if key in keys)
        return self.__class__(dat)
class Measure(Mapping):
    _combine = staticmethod(lambda _, old, new: min(2, old+new))
    def _getDefault(self): return 0
    def join(self, other, adjust):
        return self.insert(map(adjust, other.data.items()))
    def contains(self, measure):
        return all(self.get(key) >= val for key, val in measure.data.items())
class Store(Mapping):
    _combine = staticmethod(lambda _, old, new: old|new)
    def _getDefault(self): return set()
    def single(self, val): return {val}
    def contains(self, store):
        return all(self.get(key).issuperset(val)
                   for key, val in store.data.items())
sEmpty = ()
def sPush(stack, val): return (val, stack)
def sPop(stack): return stack[1]
def sPopTop(stack): return stack
def sTake(stack, n):
    taken = []
    for _ in range(n): top, stack = sPopTop(stack); taken.append(top)
    return taken, stack
def sDrop(stack, n): return sTake(stack, n)[1]
def sIter(stack):
    while stack != sEmpty: top, stack = sPopTop(stack); yield top
def sAppend(top, bot):
    for val in reversed(tuple(sIter(top))): bot = sPush(bot, val)
def sShow(stack): return str(list(sIter(stack)))
def namedTup(*args): ntup = namedtuple(*args); ntup.__str__=strTup; return ntup
################################################################
# interpreter
Binding = namedTup('Binding', 'name env')
Context = namedTup('Context', 'code stack env')
def ctxNext(ctx): return Context(sPop(ctx.code), ctx.stack, ctx.env)
def ctxPush(ctx, val): return Context(ctx.code, sPush(ctx.stack, val), ctx.env)
def ctxPopTop(ctx):
    top, stack = sPopTop(ctx.stack)
    return top, Context(ctx.code, stack, ctx.env)
def ctxAppend(ctx, stack):
    return Context(ctx.code, sAppend(stack, ctx.stack), ctx.env)
class AbstractEnv(Repr):
    _memo = {}
    @classmethod
    def new(cls, frames, mod):
        env = cls._memo.get(frames)
        if env is None:
            env = cls.__class__(frames, mod); cls._memo[frames] = env
        return env
    def __init__(self, frames, mod): self.frames = frames; self.mod = mod
    def __str__(self): return '(%s, %s)'%(self.mod, self.frames)
    def push(self, frame): return self.new((frame,)+self.frames)
    def pop(self): return self.new(self.frames[1:])
    def trim(self, sz): return self.new(self.frames[:sz])
class Config(Repr):
    def __init__(self, envSz, cont, store):
        self.envSz = envSz; self.cont = cont; self.store = store
    def __str__(self): return '%s %s'%(self.cont, self.store)
    def _newCont(self, cont, store, *args):
        return self.__class__(self.envSz, cont, store, *args)
    def _newStore(self, store, *args):
        return self._newCont(self.cont, store, *args)
    def bind(self, env, app, proc, args):
        data = proc.data; arity = data.arity; penv = data.env
        nenv = env.push(app).trim(self.envSz); store = self.store
        ndata = AbstractProcData(nenv, arity-len(args))
        nOldBnds = len(binders)-arity; binders = proc.binders
        oldBnds = binders[:nOldBnds]; binders = binders[nOldBnds:]
        bvs = zip((Binding(bn, nenv) for bn in binders), args)
        fvs = ((Binding(nm, nenv), store.get(Binding(nm, penv)))
               for nm in chain(oldBinders, proc.cloFrees))
        ncfg = self.update(chain(bvs, fvs))
        return ndata, ncfg
    def _pushCont(self, cont, contv, store): return self._newCont(cont, store)
    def pushCont(self, uid, env, ctx):
        cont = Binding(uid, env); contVal = {(ctx, self.cont)}
        store = self.store.join(Store({cont: contVal}))
        return self._pushCont(cont, contVal, store)
    def popCont(self, ctx):
        stack = ctx.stack
        store = self.store; ctxs, conts = zip(store.get(self.cont))
        ctxs = (ctxAppend(ctx, stack) for ctx in ctxs) # todo: arity?
        return zip(ctxs, (self._newCont(cont, store) for cont in conts))
    def contains(self, cfg): return self.store.contains(cfg.store)
    def join(self, cfg, *args):
        return self._newStore(self.store.join(cfg.store), *args)
    def only(self, bnds, *args):
        return self._newStore(self.store.only(bnds), *args)
    def update(self, vs, *args):
        return self._newStore(self.store.join(Store(dict(vs))))
    def print(self):
        printDiv('store'); print(strDict(self.store.data, '\n'))
# class CountConfig(Config):
#     def __init__(self, store, count):
#         super().__init__(store); self.count = count
#     def __str__(self): return '(%s %s)'%(super().__str__(), str(self.count))
#     def contains(self, cfg):
#         return self.count.contains(cfg.count) and super().contains(cfg)
#     def join(self, cfg, *args):
#         count = self.count.join(cfg.count, adjEqBinding(self.store, cfg.store))
#         return super().join(cfg, count)
#     def only(self, bnds, tms, *args):
#         return super().only(bnds, tms, self.count.only(bnds))
#     def update(self, tm, clo, bvs, fvs, *args):
#         newStore = Store(dict(chain(bvs, fvs)))
#         count = Measure(dict((bnd, 1) for bnd, _ in chain(bvs, fvs)))
#         count = self.count.join(count, adjEqBinding(self.store, newStore))
#         return self.__class__(self.store.join(newStore), count)
#     def print(self):
#         super().print(); printDiv('count')
#         print(strDict(self.count.data, '\n'))
# def adjEqBinding(store0, store1):
#     def adjust(kv):
#         bnd, cnt = kv
#         if cnt == 1 and store0.get(bnd) == store1.get(bnd): cnt = 0
#         return bnd, cnt
#     return adjust
# def newCountConfig(): return CountConfig(Store(), Measure())
class State:
    __slots__ = ['ctx', 'cfg']
    def __init__(self, ctx, cfg): self.ctx = ctx; self.cfg = cfg
    def next(self):
        ctx = self.ctx; cfg = self.cfg
        if ctx.code == sEmpty:
            return (State(ctx, cfg) for ctx, cfg in cfg.popCont(ctx))
        code, ctx = ctxPopTop(ctx); return code.eval(ctx, cfg)
class Code(Repr):
    def frees(self): return set()
    def eval(self, code, stack, env, cfg): raise NotImplementedError
def accFrees(xs): return unionReduce(x.frees() for x in xs)
def codeFrees(code): return accFrees(sIter(code))
class Lookup(Code):
    def __init__(self, name): self.name = name
    def __str__(self): return str(self.name)
    def frees(self): return {self.name}
    def eval(self, ctx, cfg):
        val = cfg.store.get(Binding(self.name, self._addr(ctx)))
        yield State(ctxPush(ctx, val), cfg)
class LookupModule(Lookup):
    def _addr(self, ctx): return ctx.env.mod
class LookupClosure(Lookup):
    def _addr(self, ctx): return ctx.env
class ApplyN(Code):
    def __init__(self, nargs): self.nargs = nargs
    def eval(self, ctx, cfg):
        procs, ctx = ctxPopTop(ctx)
        for proc in procs: yield proc.apply(self, ctx, cfg)
class Discard(Code):
    def eval(self, ctx, cfg): yield State(ctxPop(ctx), cfg)
class Halt(Code):
    def eval(self, ctx, cfg):
        while False: yield None
# todo: letrec, switch, sequence(discard), constructors, continuation reifiers

# class Expr(Repr):
#     def frees(self): raise NotImplementedError
# class Var(Expr):
#     def __init__(self, name): self.name = name
#     def __str__(self): return str(self.name)
#     def frees(self): return {self.name}
#     def eval(self, tm, cfg): return cfg.store.get(Binding(self.name, tm))
# class Apply(Expr):
#     def __init__(self, proc, args): self.proc = proc; self.args = args
#     def __str__(self):
#         return '(apply %s %s)'%(str(self.proc), strTup(self.args))
#     def frees(self): return self.proc.frees()|accFrees(self.args)
################################################################
# values
class Val(Repr): pass
class UnknownVal(Val): # todo: propositional constraints
    def __init__(self): self.cstrs = set(); self.children = {}
class SingleVal(Val):
    def __str__(self): return str(self.tag.data)
class DataVal(Val):
    def __init__(self, data=[]): self.data = data
    def __str__(self): return '%s:%s'%(self.tag.data, self.data)
class ScalarVal(DataVal): # data of None implies abstract scalar
    def __init__(self, data=None): self.data = data
class StructVal(DataVal):
    def get(self, cfg, idx): return self.cfg.get(self.data, idx)
    def set(self, cfg, idx, val): self.cfg.set(self.data, idx, val)
class AppVal(Val):
    def apply(self, nargs, ctx, cfg): NotImplementedError
AbstractProcData = namedTup('AbstractProcData', 'env arity')
# class AbstractProcData:
#     def __init__(self, env, arity): self.env = env; self.arity = arity
#     # def env(self):
#     # def arity(self): return self.arity
class ProcVal(DataVal, AppVal):
    def apply(self, app, ctx, cfg):
        code, stack, env = ctx; arity = self.data.arity; nargs = app.nargs
        napps = min(nargs, arity); args, stack = sTake(stack, napps)
        if napps > 1:
            code = sDrop(code, napps-2) # drop exhausted apps
            app, code = sPopTop(code)
        data, cfg = cfg.bind(env, app, self, args)
        if arity > nargs:
            return State(Context(code, sPush(stack, ProcVal(data)), env), cfg)
        if code != sEmpty:
            cfg = cfg.pushCont(self, data.env, Context(code, stack, env))
        return State(Context(self.code, sEmpty, data.env), cfg)
# class ContVal(AppVal):
#     def apply(self, nargs, ctx, cfg): 
# class PrimOp(AppVal):
#     def apply(self, nargs, ctx, cfg): 

class Tag(ScalarVal): pass
tagTag = Tag('Tag')
Tag.tag = tagTag
def newTy(name, cls):
    class NewVal(cls): tag = Tag(name)
    return NewVal
def newProcTy(name, code, binders, cloFrees):
    cls = newTy(name, ProcVal); cls.code = code; cls.binders = binders
    frees = codeFrees(code); cloFrees = cloFrees&frees-binders
    cls.cloFrees = cloFrees; cls.globFrees = frees - cloFrees
    return cls

# todo notes:
# per-module globals that don't require copying with other free vars
# closures/data nodes w/ de bruijn indices eventually for faster indexing
#   also allows easy testing of alpha-equivalence
#   but still keep a translation mapping from indices to original names
