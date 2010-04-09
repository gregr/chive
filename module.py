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

class ModuleManager:
    def __init__(self): self.mods = {}; self.groups = []
    def get(self, name, mkmod):
        mod = self.mods.get(name)
        if mod is None:
            group = ModuleGroup(); self.groups.append(group)
            mod = mkmod(group); self.mods[name] = mod
        else: # if active, fold up strongly-connected component
            if mod.isActive():
                mgrp = mod.group; idx = self.groups.index[mgrp]
                for group in self.groups[idx:]: mgrp.absorbGroup(group)
                self.groups = self.groups[:idx+1]
        return mod
    def __iter__(self):
        while self.groups:
            mod = self.groups[-1].top()
            if mod is None: self.groups.pop(); continue
            for expr in iter(mod): yield expr; break
class ModuleGroup:
    def __init__(self): self.mods = set(); self.modsActive = set()
    def top(self): return next(iter(self.modsActive), None)
    def add(self, mod): self.mods.add(mod); self.modsActive.add(mod)
    def absorbGroup(self, grp):
        for mod in grp.mods: mod.group = self; self.mods.add(mod)
        self.modsActive |= grp.modsActive
class Module:
    def __init__(self, name, stream, root, group):
        self.name = name; self.curNS = Namespace(root, self)
        self.exprs = Parser(self.ctx.ops).parse(name, stream)
        self.group = group; group.add(self)
    def __iter__(self):
        for expr in self.exprs: yield expr
        self.deactivate()
    def isActive(self): return self in self.group.modsActive
    def deactivate(self):
        self.group.modsActive.remove(self); self.curNS.exportAll()
class Namespace:
    def __init__(self, root, mod):
        self.mod = mod; self.ctx = freshCtx(root, self); self.exporting = True
        self.varDefs = DefManager(self.ctx.senv, self.ctx.env, self.ctx.ops)
        self.tyDefs = DefManager(self.ctx.tenv, self.ctx.env)
    def addDep(self, *args, now=False):
        if now or not self.mod.isActive(): self.varDefs.export(*args)
        else: self.varDefs.dependants.add(*args)
    def depend(self, ns, filter, now=False):
        ns.addDep(self.defVar, self.exporting, filter, now=now)
    def _defX(self, xdefs, sym, xx, export=None):
        if export is None: export = self.exporting
        xdefs.define(export, sym, xx)
    def defVar(self, sym, val, export=None, op=None):
        self._defX(self.varDefs, sym, val, export)
        if op is not None: self.defOp(sym, op)
    def defTy(self, sym, ty, export=None, _=None):
        self._defX(self.tyDefs, sym, ty, export)
    def defOp(self, sym, op): self.ctx.ops.add(EnvKey(sym), op)
    def _depX(self, xdeps, handler):
        xdeps.dependants.add(handler)
        if not self.isActive(): xdeps.exportAll()
    def depVar(self, handler): self._depX(self.varDefs, handler)
    def depTy(self, handler): self._depX(self.tyDefs, handler)
    def exportAll(self): self.tyDefs.exportAll(); self.varDefs.exportAll()
class DefManager:
    def __init__(self, xenv, env, ops=None):
        self.xenv = xenv; self.env = env; self.ops = ops or Env()
        self.exportedNames = set(); self.dependants = set()
    def _addName(self, exporting, sym):
        if exporting: self.exportedNames.add(EnvKey(sym))
    def refer(self, exporting, sym, srcEnv):
        self.addName(exporting, sym); referX(srcEnv, self.xenv, sym)
    def define(self, exporting, sym, val):
        self.addName(exporting, sym); bindX(self.xenv, self.env, sym, val)
    def export(self, defX, shouldExport, filter):
        hideNames, names, rename = filter
        if hideNames: exports = self.exportedNames-names
        else: exports = names
        if rename:
            nold, nnew = tuple(zip(rename)); exports-=nold; exports+=nnew
        for name in exports:
            defX(sym, getX(self.xenv, self.env, name.sym), shouldExport,
                 self.ops.get(name))
    def exportAll(self):
        for exArgs in self.dependants: self.export(*exArgs)
        self.dependants.clear()
