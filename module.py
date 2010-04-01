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
class ModuleGroup:
    def __init__(self): self.mods = set(); self.modsActive = set()
    def add(self, mod): self.mods.add(mod); self.modsActive.add(mod)
    def absorbGroup(self, grp):
        for mod in grp.mods: mod.group = self; self.mods.add(mod)
        self.modsActive |= grp.modsActive
class Module:
    def __init__(self, ctx, name, stream, group):
        self.name = name; self.ctx = ctx.copy(); self.ctx.mod = self;
        self.ctx.tenv = Env(ctx.tenv); self.ctx.senv = Env(ctx.senv)
        self.ctx.attr = None; self.ctx.hist = nil
        self.stream = stream; self.group = group; group.add(self)
    def isActive(self): return self in self.group.modsActive
    def deactivate(self): self.group.modsActive.remove(self)
