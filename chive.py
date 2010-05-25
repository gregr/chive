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

import optparse

def options():
    op = optparse.OptionParser('usage: %prog [options] [PROGRAM [ARGS]]')
    op.add_option('-i', '--interact', dest='interact', default=False,
                  action='store_true', help='evaluate interactively')
    op.add_option('-b', '--bootstrap', dest='bootstrap', default=False,
                  action='store_true', help='evaluate at the bootstrap phase')
    opts, args = op.parse_args()
    opts.interact = opts.interact or len(args)==0
    return opts, args
oas = options()
from semantics import *
splash = """chive 0.0.0: help system is still a work in progress..."""
def run(opts, args):
    root = Root(()); thread = Thread(root)
    bootMod = root.emptyModule(); primMod.openIn(bootMod.nspace)
    bootMod.name = 'boot'
    if opts.bootstrap: mod = bootMod
    else:
#        coreMod = evalFile(thread, bootMod, 'boot.chive') # todo
        coreMod = primMod # for now
        mod = root.emptyModule(); coreMod.openIn(mod.nspace); mod.name = 'user'
    if len(args) > 0: evalFile(thread, mod, args[0])
    if opts.interact: print(splash); interact(thread, mod)
    return thread, mod
if __name__ == '__main__': thread, mod = run(*oas)
