#!/usr/bin/env python

import re
import db2rst
import lxml.etree as ET

from cStringIO  import StringIO
import sys


latexQuotes = r"(``|'')"
def latexQuotesFmt(match):
    return '"'

def delimited(l,r,sl,sr):
    r = re.compile(l + '(?P<value>.+?)' + r,re.DOTALL)
    def fmt(match):
        return sl + match.group('value') + sr
    return (r,fmt)


token = r'(?P<start>[^`])`(?P<name>[\w-]+)(?P<term>\s|,|\.|<|>|:|;|\)|")'
def tokenFmt(match):
    str = match.group('name')
    return match.group('start') + ':token:`' + re.sub(r'-','_',str) + "`" + match.group('term')


# We check for whitespace before and after -- if it is not present,
# then we throw in '\ ' to separate it.
inlinecode = re.compile(r'(?P<prespace>\s)?\[\[(?P<lang>\w:)?(?P<code>.*?)\]\](?P<postspace>\s)?')

def inlineCodeFmt(match):
    str = match.group('code')

    start = r'\1``\2``\3'

    if not match.group('prespace'):
        start = r'\ ' + start
    else:
        start = match.group('prespace') + start

    if not match.group('postspace'):
        start = start + r'\ '
    else:
        start = start + match.group('postspace')


    # Lift leading/trailing whitespace out
    str1 = re.sub(r'^(\s*)(.*?)(\s*)$',start,str)

    # Lift emphasis out
    str2 = re.sub(r'(?:\s*)\$(?:\s*)(\w+?)(?:\s*)\$(\s*)',r'``\ *\1*\ \2``',str1)

    str3 = re.sub(r'````',r'',str2)

    # print '%s => %s => %s => %s' % (str,str1,str2,str3)
    return str3


blockcode = re.compile('\[\[(?P<lang>\w:)?(?P<code>.*\n((?:\|\|).*\n)*)\]\]')
def blockCodeFmt(match):
    str = match.group('code')

    tmp = re.sub(r'(?:\|\|)?(.*\n)',r'    \1',str)

    # Skip leading newlines
    lines = tmp.split('\n')
    for i in range(len(lines)):
        if lines[i].strip() != '' :
            break
    # Figure out how far that the first line is indented, since reST requires exactly 2 space
    # indent for first line.
    offset = len(lines[i]) - len(lines[i].lstrip())


    lang = match.group('lang')
    if not lang:
        lang = "specware"
    elif lang == 'L:':
        lang = "common-lisp"

    res = "\n.. code-block:: %s\n\n" % lang
    for l in lines[i:]:
        s = l.lstrip()
        n = len(l) - len(s)
        pad = max(0,(n-offset))
        # Pad it out
        res += '   ' + (' '* (max(0, (n-offset)))) + s + '\n'

    return res

blocksyntax = re.compile('\<\<(?P<code>.*\n((?:\|\|).*\n)*)\>\>')
def blockSyntaxFmt(match):
    str = match.group('code')
    # First, remove all of the leading pipes
    ss = re.sub(r'\|\|',r'',str)

    # Remove all of the blank lines
    ss = re.sub(r'\n\n','',ss)

    # Split this in to a set of productions.
    ss = re.split(r'`([\w-]+)\s+?::=', ss)
    # 0th element is ignored

    # Left-hand sides correspond to odd positions
    lhs = ss[1::2]
    # Right-hand sides correspond to even positions
    rhs = ss[2::2]

    res = '\n.. productionlist::'

    for (l,r) in zip(lhs,rhs):

        # Convert underscores to dashes
        l = l.replace('-','_')
        # A nonterminal is ` followed by word character or dashes
        tmp = re.sub(r'`(?P<id>[\w-]+)', lambda m: '`' + m.group('id').replace('-','_') + '`' ,r)

        # Convert single-quoted things to strings
        tmp = re.sub(r'\'([^\s]+)(\s)',r'"\1"\2',tmp)

        # Remove newlines on rhs
        tmp = re.sub(r'\n',r'',tmp)
        # Split up the right hand side alternatives

        alts = re.split(r'[^\"]\|[^\"]',tmp)
        header = '\n  ' + l + ':'
        indent = (' ' * (len(header) - 2)) + ':'
        for a in alts:
            res += header + ' ' + a.strip()
            header = ' | \n' + indent

    return res + '\n'



test = """

[[ start
|| spec foo
||   type x
|| endspec
]]


[[ block 2
||
]]


Some inline [[ code ]]


<<
||`list-display ::= '[ `list-display-body '] | Foo
||
||`list-display-body ::= [ `expression { , `expression }* ]
>>
"""


inline = 'here is some inline code [[x + 2]] and [[[]]]'


transforms = [(latexQuotes,latexQuotesFmt)
              ,(inlinecode,inlineCodeFmt)
              ,(blockcode,blockCodeFmt)
              ,(blocksyntax,blockSyntaxFmt)
              ,(token,tokenFmt)
              ,delimited('<<','>>','``','``')
              ,delimited('<"', '">','``','``')
              ,delimited('\$','\$','*','*')]




entities = """<?xml version="1.0" encoding="utf-8"?>
<!DOCTYPE root [
<!ENTITY Specware "Specware">
<!ENTITY V "4.2">
<!ENTITY SpecwareV "&Specware; &V;">
<!ENTITY Metaslang "Metaslang">
<!ENTITY xemacs "XEmacs">
<!ENTITY lt "&#60;">
<!ENTITY gt "&#62;">
<!ENTITY emdash "--">
<!ENTITY KI "Kestrel Institute">
<!ENTITY KT "Kestrel Technology LLC">
<!ENTITY KDC "Kestrel Development Corporation">
<!ENTITY copyrightholder "&KDC;">
<!ENTITY copyrightholder2 "&KT;">
<!ENTITY trademarkholder "&KDC;">
<!ENTITY undefined "<replaceable>undefined</replaceable>">
<!ENTITY List "List">
<!ENTITY List "List">

]>
"""

table = r' & | && | < | > |<=>|=>|<\*>|<=|\(<\)|<<|<-|``&&``|``<<``'




def main(fname=None):

    if fname is None:
        fname = sys.argv[1]

    with open(fname + '.glm') as f:
        cnts = f.read()
        for (r,fmt) in transforms:
            cnts = re.sub(r,fmt,cnts)

        cnts = re.sub(r'&(.*?);', r'|\1|',cnts)
        def cvt(match):
            op = match.group(0)
            return re.sub(r'<',r'&lt;',re.sub(r'>',r'&lt;',re.sub(r'&',r'&amp;', op)))

        cnts = re.sub(table,cvt,cnts)


    with open(fname + '.cvt','w') as f:
        f.write(entities + cnts)

    parser = ET.XMLParser(resolve_entities=False)
    tree = ET.parse(StringIO(entities + cnts),parser=parser)
    with open(fname + '.rst','w') as f:
        f.write(str(db2rst.proctree(tree)))

    print "Done converting"



if __name__ == '__main__':
    main()
