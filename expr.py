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

from data import typeErr, checkTagBounds

def final(val): return None, val
def cont(ctx, expr): return ctx, expr
def evalExpr(ctx, expr, tag=None): # tail-call trampoline
    while ctx is not None: ctx, expr = expr.eval(ctx)
    if tag is not None: checkTag(ctx, tag, expr)
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
class ConsNodeTag(Constr):
    def __init__(self, name, fields): self.name = name; self.fields = fields
    def eval(self, ctx):
        ftags = []
        for fname in fields:
            ftag = ctx.env.get(fname)
            if ftag is None:
                ftag = NodeTag(str(fname), None)
                ctx.env.add(fname, ftag)
            ftags.append(ftag)
        tag = ctx.env.get(self.name)
        if tag is None:
            tag = NodeTag(str(self.name), ftags)
            ctx.env.add(self.name, tag)
        if not isinstance(tag, NodeTag):
            typeErr(ctx, "name already in use: '%s'"%self.name)
        return final(tag)
class ConsNode(Constr):
    def __init__(self, tag, cargs, ctx):
        checkTagBounds(ctx, tag, len(cargs),
                       "too many constructor arguments: '%d'")
        self.tag = tag; self.cargs = cargs
    def eval(self, ctx):
        cargs = [evalExpr(ctx, carg, ctag)
                 for carg, ctag in zip(self.cargs, self.tag.fieldTags)]
        return final(node(self.tag, *cargs))
class ConsArrayTag(Constr): pass
class ConsArray(Constr): pass

################################################################
class Access(Expr): pass
class NodeGetTag(Access):
    def __init__(self, node): self.node = node
    def eval(self, ctx):
        val = evalExpr(ctx, self.node); checkIsNode(ctx, val)
        return final(node_tag(val))
class NodeAccess(Access):
    def __init__(self, tag, index, node, ctx):
        checkTagBounds(ctx, tag, index, "node index out of bounds: '%d'")
        self.tag = tag; self.index = index+1; self.node = node
    def _evalNode(self, ctx):
        node = evalExpr(ctx, self.node, self.tag)
        return node
class NodeUnpack(NodeAccess):
    def eval(self, ctx):
        return final(nodeUnpack(self._evalNode(ctx), self.index))
class NodePack(NodeAccess):
    def __init__(self, rhs, *args):
        super().__init__(*args)
        self.rhs = rhs
    def eval(self, ctx):
        nodePack(self._evalNode(ctx), self.index, evalExpr(ctx, rhs, self.tag))
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
    def __init__(self, discrimTag, discrim, default, alts):
        self.discrimTag = discrimTag
        self.discrim = discrim; self.default = default; self.alts = alts
    def eval(self, ctx):
        discrim = evalExpr(ctx, self.discrim, self.discrimTag)
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
#         senv = evalExpr(ctx, self.senv, envTag)
#         env = evalExpr(ctx, self.env, envTag)
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
# class Evaluate(Meta):
#     def eval(self, ctx): return final(evaluate(*self._evalArgs(ctx)))
