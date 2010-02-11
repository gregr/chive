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

from data import checkNodeBounds

class EvalError(Exception): pass
def evalErr(ctx, msg): raise EvalError(ctx, msg)

def evalExpr(ctx, expr): pass
def final(val): return None, val
def cont(ctx, expr): return ctx, expr

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
        if val is None: evalErr(ctx, "unbound variable '%s'"%self.name)
        return final(val)

################################################################
class Constr(Expr): pass
class ConsNode(Constr):
    def __init__(self, tag, cargs, ctx):
        checkNodeBounds(ctx, tag, len(cargs),
                        "too many constructor arguments: '%d'")
        self.tag = tag; self.cargs = cargs
    def eval(self, ctx):
        cargs = [evalExpr(ctx, carg) for carg in self.cargs]
        return final(node(self.tag, *cargs))
class ConsProc(Constr):
    names = nameGen(['#proc_'])
    def __init__(self, binders, body):
        self.name = self.names.next()
        self.binders = binders
        self.body = body
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
            typeErr(ctx, "chosen tag name is already in use: '%s'"%self.name)
        return final(tag)

################################################################
class Access(Expr): pass
class NodeGetTag(Access):
    def __init__(self, node): self.node = node
    def eval(self, ctx): return final(node_tag(evalExpr(ctx, self.node)))
class NodeAccess(Access):
    def __init__(self, tag, index, node, ctx):
        checkNodeBounds(ctx, tag, index, "node index out of bounds: '%d'")
        self.tag = tag; self.index = index+1; self.node = node
    def _evalNode(self, ctx):
        node = evalExpr(ctx, self.node)
        if node_tag(node) != self.tag:
            typeErr(ctx, "tag mismatch: expected '%s', found '%s'"%
                    (self.tag, node_tag(node)))
        return node
class NodeUnpack(NodeAccess):
    def eval(self, ctx): return final(self._evalNode(ctx)[self.index])
class NodePack(NodeAccess):
    def __init__(self, rhs, *args):
        super().__init__(*args)
        self.rhs = rhs
    def eval(self, ctx):
        rhs = evalExpr(ctx, rhs) # todo: match elem tag once they are tracked
        self._evalNode(ctx)[self.index] = rhs
        return final(unit)

################################################################
class Seq(Expr): pass
class Apply(Expr): pass
class Switch(Expr): pass

################################################################
class Throw(Expr): pass # could be a proc
class Catch(Expr): pass

################################################################
class Delay(Expr): pass
class Force(Expr): pass # could be a proc (eval then update)

################################################################
class Meta(Expr):
    def __init__(self, senv, env, form):
        self.senv = senv; self.env = env; self.form = form
    def _evalArgs(self, ctx):
        senv = fromEnv(evalExpr(ctx, self.senv)) # todo: type check
        env = fromEnv(evalExpr(ctx, self.env)) # todo: type check
        form = evalExpr(ctx, self.form)
        ctx = ctx.copy()
        ctx.hist = nil
        ctx.senv = senv
        ctx.env = env
        return ctx, form
class Expand(Meta):
    def eval(self, ctx):
        ctx, form = expand(*self._evalArgs(ctx))
        return final(synclo_new(toEnv(ctx.senv), nil, form))
class Evaluate(Meta): pass
    def eval(self, ctx): return final(evalData(*self._evalArgs(ctx)))
