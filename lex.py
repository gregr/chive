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

from data import nil, toInt, toFloat, toChar, toString
import re

tokenTypes = ('whitespace', 'comment', 'indentation', 'syntax',
              'operator', 'ident', 'literal')
ignoredTokenTypes = ('whitespace', 'comment')

def makeIdent(s): # strip escapes
    return "\\".join(ss.replace('\\', '') for ss in s.split('\\\\'))
def makeIdentOp(s): return makeIdent(s[1:-1])
def makeInt(s): return toInt(int(s)) # todo: Iu32, Is32, etc.
def makeFloat(s): return toFloat(float(s))
def makeChar(s): return toChar(eval(s))
def makeString(s): return toString(eval(s))

def makeTokClass(tokSpec): return (re.compile(tokSpec[0]),)+tokSpec[1:]
def makeTokClasses(tokSpecs): return [makeTokClass(c) for c in tokSpecs]
operPat = '#?[`~!@$%^&*\\=+|;:,.<>/?-]+'
identPat = r'#?([a-zA-Z_]|(\\.))([-]?(\w|(\\.)))*[!?]*'
openBracePat = r'#?[(\[{]'
closeBracePat = r'[)\]}]'
bracePat = '(%s|%s)'%(openBracePat, closeBracePat)
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
        (r'##.*', 'comment', str),
        (operPat, 'operator', str),
        (bracePat, 'syntax', str),
        ))
tokClassesNonWhitespace = tokClassesNonDelimiter+tokClassesDelimiter

class SrcAttr:
    def __init__(self, streamName, srcs, start, end):
        self.streamName = streamName
        self.srcs = list(map(str.rstrip, srcs))
        self.start = start; self.end = end
        self.subs = nil
    def copy(self):
        return SrcAttr(self.streamName, self.srcs, self.start, self.end)
    def location(self):
        if self.start[0] == self.end[0]:
            loc='%d,%d-%d'%(self.start[0], self.start[1], self.end[1])
        else: loc='%d,%d-%d,%d'%(self.start[0], self.start[1],
                                 self.end[0], self.end[1])
        return self.streamName+' '+loc
    def highlight(self, prefix):
        lead = prefix
        margin = ' '*len(lead)
        def hl(src, pref, col, length):
            return pref+src+'\n'+margin+(' '*col)+('^'*length)
        if len(srcs) > 1:
            return ([hl(self.src[0], lead, self.start[1],
                        len(self.src[0])-self.start[1])]+
                    [hl(src, margin, 0, len(src)) for src in self.srcs[1:-1]]+
                    [hl(self.src[-1], margin, 0,
                        len(self.src[-1])-self.end[1]-1)])
        else: return hl(self.src[0], lead, self.start[1],
                        self.end[1]-self.start[1]+1)
    def show(self): return self.location()+':\n'+self.highlight('')
    def __repr__(self): return 'SrcAttr(%r, %r)'%(self.location(), self.srcs)

class Token:
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

class LexError(Exception): pass
def lexErr(attr, msg): raise LexError(attr, msg)

def tokensInLine(streamName, src, line):
    col = 0
    cur = src.rstrip()
    def attr(length):
        return SrcAttr(streamName, [src], (line, col), (line, col+length-1))
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
            if tokClass in tokClassesDelimiter:
                tokClasses = tokClassesNonWhitespace
            else: tokClasses = tokClassesDelimiter
            if tty not in ignoredTokenTypes:
                if firstToken:
                    yield indent
                    firstToken = False
                yield Token(tty, tval, attr(cs))
            col+=cs

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

def tokens(streamName, stream):
    lineNum = 0
    for line, lineNum in logicalLines(stream):
        for token in tokensInLine(streamName, line, lineNum): yield token
    yield Token('indentation', -1,
                SrcAttr(streamName, [''], (lineNum+1, 0), (lineNum+1, 0)))

def _test(s):
    from io import StringIO
    for t in tokens('lex.test', StringIO(s)): print(t)

if __name__ == '__main__':
    _test(r'(f abc 2 - 3 -4 \5\+def)')
    _test('hello? world!\n  4+ 3\n\nthis is a hyphen-ident'+
          '\n  5 - 6\n  \n## comments\n\n#test #(#+-)\n')
