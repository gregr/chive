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

import re

tokenTypes = ('whitespace', 'comment', 'meta', 'indentation',
              'syntax', 'operator', 'ident', 'literal')
ignoredTokenTypes = ('whitespace', 'comment')

def makeIdent(s): # strip escapes
    return "\\".join(ss.replace('\\', '') for ss in s.split('\\\\'))
def makeIdentOp(s): return makeIdent(s[1:-1])
def makeInt(s): return ('int', int(s)) # todo: Iu32, Is32, etc.
def makeFloat(s): return ('float', float(s))
def makeChar(s): return ('char', eval(s))
def makeString(s): return ('string', eval(s))

def makeTokClass(tokSpec): return (re.compile(tokSpec[0]),)+tokSpec[1:]
def makeTokClasses(tokSpecs): return [makeTokClass(c) for c in tokSpecs]
operPat = '[`~!@$%^&*\\=+|;:,.<>/?-]+'
identPat = r'([a-zA-Z_]|(\\.))([-]?(\w|(\\.)))*[!?]*'
bracePat = r'[()\[\]{}]'
tokClassesWhitespace = makeTokClasses((
        (r'\s+', 'whitespace', len),
        ))
tokClassesNonDelimiter = makeTokClasses((
        (identPat, 'ident', makeIdent),
        ('`%s`'%identPat, 'operator', makeIdentOp),
        (r'-?(\d+\.\d+)([eE][+-]?\d+)?', 'literal', makeFloat),
        (r'-?(0x)?\d+', 'literal', makeInt),
        (r"'((\\.)|[^\\'])'", 'literal', makeChar),
        (r'"((\\.)|[^\\"])*"', 'literal', makeString),
        ))
tokClassesDelimiter = tokClassesWhitespace+makeTokClasses((
        (operPat, 'operator', str),
        (r'##.*', 'comment', str),
        ((r'#(('+operPat+')|(((\\.)|\w)+))'), 'meta', str),
        (bracePat, 'syntax', str),
        ('#'+bracePat, 'metasyntax', str),
        ))
tokClassesNonWhitespace = tokClassesNonDelimiter+tokClassesDelimiter

class SrcAttr(object):
    def __init__(self, src, line, col, length):
        self.src = src; self.line = line; self.col = col; self.length = length
    def location(self):
        return '%d,%d-%d'%(self.line, self.col, self.col+self.length)
    def show(self, prefix):
        lead = prefix+self.location()+': '
        highlight = (' '*(len(lead)+self.col))+('^'*self.length)
        return lead+self.src.rstrip()+'\n'+highlight
    def __repr__(self): return 'SrcAttr(%r, %r)'%(self.location(), self.src)

class Token(object):
    def __init__(self, ty, val, attr):
        assert ty in tokenTypes
        self.ty = ty; self.val = val; self.attr = attr
    def __repr__(self): return 'Token%r'%((self.ty, self.val, self.attr),)

def matchAgainst(tokClasses, s):
    for tokClass in tokClasses:
        r, tokenType, tokEval = tokClass
        m = r.match(s)
        if m is not None:
            end = m.end()
            return (tokenType, tokEval(s[:end])), s[end:], end, tokClass
    return (None, None), s, 0, None

class LexError(StandardError): pass
def lexErr(msg, attr): raise LexError, (msg, attr)

def tokensInLine(src, line):
    col = 0
    cur = src.rstrip()
    def attr(length): return SrcAttr(src, line, col, length)
    if cur:
        (tty, tval), cur, cs, _ = matchAgainst(tokClassesWhitespace, cur)
        if tty is not None:
            indent = Token('indentation', tval, attr(cs))
            col+=cs
        else: indent = Token('indentation', 0, attr(0))
        tokClasses = tokClassesNonWhitespace
        firstToken = True
        while cur:
            (tty, tval), cur, cs, tokClass = matchAgainst(tokClasses, cur)
            if tty is None:
                if tokClasses is tokClassesDelimiter:
                    (tty, tval), _, cs, _ = matchAgainst(
                                             tokClassesNonWhitespace, cur)
                    if tty is not None:
                        lexErr('expected delimiter; found %s' % tty, attr(cs))
                lexErr('unknown token type', attr(0))
            col+=cs
            if tokClass in tokClassesDelimiter:
                tokClasses = tokClassesNonWhitespace
            else: tokClasses = tokClassesDelimiter
            if tty not in ignoredTokenTypes:
                if firstToken:
                    yield indent
                    firstToken = False
                yield Token(tty, tval, attr(cs))

def logicalLines(stream):
    prevLine = ''
    lineNum = 0
    skippedLines = 0
    for line in stream:
        lineNum += 1
        if line.endswith('\\\n'):
            prevLine += line[:-2]
            skippedLines += 1
        else:
            yield prevLine+line, lineNum-skippedLines
            prevLine = ''
            skippedLines = 0
    if prevLine: yield prevLine, lineNum

def tokens(stream):
    lineNum = 0
    for line, lineNum in logicalLines(stream):
        for token in tokensInLine(line, lineNum): yield token
    yield Token('indentation', -1, SrcAttr('', lineNum+1, 0, 0))

def _test(s):
    from StringIO import StringIO
    for t in tokens(StringIO(s)): print t

if __name__ == '__main__':
    _test(r'(f abc 2 - 3 -4 \5\+def)')
    _test('hello? world!\n  4+ 3\n\nthis is a hyphen-ident'+
          '\n  5 - 6\n  \n## comments\n\n')
