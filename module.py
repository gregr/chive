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

class Module:
    def __init__(self, name, stream, root):
        self.name = name; self.curNS = Namespace(root, self)
        self.exprs = Parser(self.ctx.ops).parse(name, stream)
        self.active = True
    def __iter__(self):
        for expr in self.exprs: yield expr
        self.active = False
    def isActive(self): return self.active
class Namespace:
    def __init__(self, root, mod):
        self.mod = mod; self.ctx = freshCtx(root, self)
        self.exportedNames = set(); self.exporting = True
    def _addName(self, export, sym):
        if export or self.exporting: self.exportedNames.add(EnvKey(sym))
    def refer(self, ctxFrom, symFrom, symTo=None, export=None):
        self.addName(export, symTo)
        referVar(ctxFrom, self.ctx, symFrom, symTo)
    def define(self, sym, val, export=None):
        self.addName(export, sym); bindVar(self.ctx, self.env, sym, val)
    def defOp(self, sym, op): self.ctx.ops.add(EnvKey(sym), op)
    def export(self, ns, filter):
        hideNames, names, rename = filter
        if hideNames: exports = self.exportedNames-names
        else: exports = names
        for name in exports:
            nnew = rename.get(name)
            if nnew is None: nnew = name
            ns.refer(self.ctx, name.sym, nnew.sym)
            op = self.ctx.ops.get(name)
            if op is not None: ns.defOp(nnew.sym, op)
