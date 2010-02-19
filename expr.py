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

from data import typeErr

def final(val): return None, val
def cont(ctx, expr): return ctx, expr
def evalExpr(ctx, expr, ty=None): # tail-call trampoline
    while ctx is not None: ctx, expr = expr.eval(ctx)
    if ty is not None: ty.checkTy(expr)
    return expr # when ctx is None, expr will be a final value

class Expr:
    def pretty(self): return 'todo'

################################################################
class Atom(Expr): pass
class PrimVal(Atom):
    def __init__(self, val): self.val = val
    def eval(self, ctx): return final(self.v)
class Var(Atom):
    def __init__(self, name): self.name = name
    def eval(self, ctx):
        val = ctx.env.get(self.name)
        if val is None: typeErr(ctx, "unbound variable '%s'"%self.name)
        return final(val)

################################################################
class Constr(Expr): pass
class ConsProc(Constr):
    def __init__(self, name, binders, body):
        self.name = name; self.binders = binders; self.body = body
    def eval(self, ctx):
        return final(proc_new(self.name, self.binders, self.body, ctx))
class ConsNodeTy(Constr):
    def __init__(self, name, els): self.name = name; self.els = els
    def eval(self, ctx):
        elts = []
        for el in self.els:
            elt = ctx.env.get(el)
            if elt is None:
                elt = NodeType(str(el), None)
                ctx.env.add(el, elt)
            elts.append(elt)
        tag = ctx.env.get(self.name)
        if tag is None:
            tag = NodeType(str(self.name), elts)
            ctx.env.add(self.name, tag)
        else:
            if not isinstance(tag, NodeType) or tag.elts is not None:
                typeErr(ctx, "name already in use: '%s'"%self.name)
            tag.__init__(str(self.name), elts = elts)
        return final(tag)
class ConsNode(Constr):
    def __init__(self, ty, cargs, ctx):
        ty.checkIndex(len(cargs),
                      'incorrect number of constructor arguments:', True)
        self.ty = ty; self.cargs = cargs
    def eval(self, ctx):
        cargs = [evalExpr(ctx, carg) for carg in self.cargs]
        return final(node(self.ty, *cargs))
class ConsArrayTy(Constr): pass
class ConsArray(Constr): pass

################################################################
class Access(Expr): pass
class NodeGetTag(Access): # todo: proc?
    def __init__(self, node): self.node = node
    def eval(self, ctx): return final(getTy(evalExpr(ctx, self.node, anyTy)))
class NodeAccess(Access):
    def __init__(self, ty, index, node, ctx):
        ty.checkIndex(index, 'node index out of bounds:')
        self.ty = ty; self.index = index; self.node = node
    def _evalNode(self, ctx):
        return evalExpr(ctx, self.node, self.ty)
class NodeUnpack(NodeAccess):
    def eval(self, ctx):
        return final(self.ty.unpackEl(self._evalNode(ctx), self.index))
class NodePack(NodeAccess):
    def __init__(self, rhs, *args):
        super().__init__(*args)
        self.rhs = rhs
    def eval(self, ctx):
        self.ty.packEl(self._evalNode(ctx), self.index, evalExpr(ctx, rhs))
        return final(unit)
# todo: array access

################################################################
class Seq(Expr):
    def __init__(self, exprs): self.exprs = exprs[:-1]; self.last = exprs[-1]
    def eval(self, ctx):
        for expr in self.exprs: evalExpr(ctx, expr)
        return cont(ctx, self.last)
class Apply(Expr):
    def __init__(self, proc, args): self.proc = proc; self.args = args
    def eval(self, ctx): return applyFull(ctx, self.proc, self.args)
class Switch(Expr):
    def __init__(self, discrimTy, discrim, default, alts):
        self.discrimTy = discrimTy
        self.discrim = discrim; self.default = default; self.alts = alts
    def eval(self, ctx):
        discrim = evalExpr(ctx, self.discrim, self.discrimTy)
        body = self.alts.get(discrim)
        if body is None: body = self.default
        return cont(ctx, body)

################################################################
class Throw(Expr): pass # could be a proc
class Catch(Expr): pass

################################################################
class Delay(Expr): pass
class Force(Expr): pass # could be a proc (eval then update)

################################################################
# class Meta(Expr):
#     def __init__(self, senv, env, form):
#         self.senv = senv; self.env = env; self.form = form
#     def _evalArgs(self, ctx):
#         senv = evalExpr(ctx, self.senv, envTy)
#         env = evalExpr(ctx, self.env, envTy)
# form = evalExpr(ctx, self.form) # todo: check proper form tag
#         ctx = ctx.copy()
#         ctx.hist = nil
#         ctx.senv = fromEnv(senv)
#         ctx.env = fromEnv(env)
#         return ctx, form
# class Expand(Meta):
#     def eval(self, ctx):
#         ctx, form = expand(*self._evalArgs(ctx))
#         return final(synclo_new(toEnv(ctx.senv), nil, form))

