import re, sys

src = open(sys.argv[1]).read()

# Strip PDF-only layout/colour directives before pandoc HTML/MathJax conversion.
src = re.sub(r'\\AtBeginDocument\{.*?\n\}\n', '', src, flags=re.S)
src = re.sub(r'\\needspace\{[^}]*\}\n?', '', src)
src = src.replace('\\FloatBarrier\n', '').replace('\\FloatBarrier', '')
src = src.replace('\\clearpage\n', '').replace('\\clearpage', '')
src = re.sub(r'\\begin\{description\}\[[^\]]*\]', r'\\begin{description}', src)
src = re.sub(r'\\begin\{itemize\}\[[^\]]*\]', r'\\begin{itemize}', src)
src = re.sub(r'\\begin\{enumerate\}\[[^\]]*\]', r'\\begin{enumerate}', src)

# Colour by role on the HTML page via MathJax \class, styled by head.html CSS.
def swap(old, new):
    global src
    assert src.count(old) == 1, old
    src = src.replace(old, new)


swap(r'\newcommand{\sep}{\mathrel{\#}}', r'\newcommand{\sep}{\mathrel{\class{asr}{\#}}}')
for n in ['keep', 'init', 'grow', 'any']:
    swap(r'\newcommand{\%s}{\kw{%s}}' % (n, n), r'\newcommand{\%s}{\class{chg}{\mathsf{%s}}}' % (n, n))
swap(r'\newcommand{\old}{\kw{old}}', r'\newcommand{\old}{\class{asr}{\mathsf{old}}}')
for macro, word in [('val', 'values'), ('st', 'spines'), ('fld', 'fields')]:
    swap(r'\newcommand{\%s}{\kw{%s}}' % (macro, word), r'\newcommand{\%s}{\class{reg}{\mathsf{%s}}}' % (macro, word))
swap(r'\newcommand{\lean}[1]{\texttt{\small #1}}', r'\newcommand{\lean}[1]{\emph{\texttt{#1}}}')

open(sys.argv[2], 'w').write(src)
