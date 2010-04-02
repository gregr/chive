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
    def __init__(self, ctx, implicitStream):
        self.ctx = ctx; self.mods = {}; self.groups = []
        self.streams = {}; self.implicitStream = implicitStream
    def _getStream(self, name):
        stream = self.streams.get(name)
        if stream is None:
            stream = self.implicitStream(name)
            self.explicitStream(name, stream)
        return stream
    def explicitStream(self, name, stream):
        assert name not in self.streams, name
        self.streams[name] = stream
    def get(self, name):
        mod = self.mods.get(name)
        if mod is None:
            group = ModuleGroup(); self.groups.append(group)
            mod = Module(self.ctx, name, self._getStream(name), group)
            self.mods[name] = mod
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
class DefManager:
    def __init__(self, xenv, env):
        self.xenv = xenv; self.env = env; self.exportedNames = set()
        self.dependants = set()
    def define(self, exporting, sym, val):
        if exporting: self.exportedNames.add(EnvKey(sym))
        bindX(self.xenv, self.env, sym, val)
    def export(self, ops=None):
        if ops is None: ops = Env()
        for defX, including, excluding in self.dependants:
            if excluding is None: exports = set(including.keys())
            else: exports = self.exportedNames-excluding
            for name in exports:
                sym = including.get(name)
                if sym is None: sym = name.sym
                defX(sym, getX(self.xenv, self.env, name.sym), ops.get(name))
        self.dependants.clear()
class Module:
    def __init__(self, ctx, name, stream, group):
        self.name = name; self.exporting = True
        self.ctx = ctx.branch(); self.ctx.mod = self
        self.ctx.attr = None; self.ctx.hist = nil
        self.varDefs = DefManager(ctx.senv, ctx.env)
        self.tyDefs = DefManager(ctx.tenv, ctx.env)
        self.exprs = Parser(self.ctx.ops).parse(name, stream)
        self.group = group; group.add(self)
    def __iter__(self):
        for expr in self.exprs: yield expr
        self.deactivate()
    def isActive(self): return self in self.group.modsActive
    def deactivate(self): self.group.modsActive.remove(self); self.export()
    def _defX(self, xdefs, sym, xx): xdefs.define(self.exporting, sym, xx)
    def defVar(self, sym, val, op=None):
        self._defX(self.varDefs, sym, val)
        if op is not None: self.defOp(sym, op)
    def defTy(self, sym, ty, _=None): self._defX(self.tyDefs, sym, ty)
    def defOp(self, sym, op): self.ctx.ops.add(EnvKey(sym), op)
    def _depX(self, xdeps, handler, ops=None):
        xdeps.dependants.add(handler)
        if not self.isActive(): xdeps.export(ops)
    def depVar(self, handler): self._depX(self.varDefs, handler, self.ctx.ops)
    def depTy(self, handler): self._depX(self.tyDefs, handler)
    def export(self): self.tyDefs.export(); self.varDefs.export(self.ctx.ops)
