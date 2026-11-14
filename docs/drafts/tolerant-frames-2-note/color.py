"""note.tex -> note-color.tex: the same text with colour and code highlighting for the PDF.
note.tex stays the plain source; this is a presentation pass."""
import re

t = open('note.tex').read()


def rep(old, new, count=1):
    global t
    assert t.count(old) == count, (old, t.count(old))
    t = t.replace(old, new)


# ---- code highlighting inside \code{...}
KW = r'const|let|var|for|while|if|else|return|function|type|readonly|null|undefined|true|false|new|typeof'


def hl(arg):
    keep = []

    def stash(s):
        keep.append(s)
        return '\x00%d\x00' % (len(keep) - 1)

    arg = re.sub(r'/\*\*.*?\*/', lambda m: stash(r'\ccm{' + m.group(0) + '}'), arg)
    arg = re.sub(r'"[^"]*"', lambda m: stash(r'\cs{' + m.group(0) + '}'), arg)
    arg = re.sub(r'@[A-Za-z]+', lambda m: stash(r'\cann{' + m.group(0) + '}'), arg)
    arg = re.sub(r'(?<![\\A-Za-z0-9_])(' + KW + r')(?![A-Za-z0-9_])', lambda m: stash(r'\ck{' + m.group(1) + '}'), arg)
    arg = re.sub(r'(?<![\\A-Za-z_.\d\x00])\d+(?![A-Za-z_\d\x00])', lambda m: stash(r'\cn{' + m.group(0) + '}'), arg)
    for _ in range(3):
        arg = re.sub('\x00(\\d+)\x00', lambda m: keep[int(m.group(1))], arg)
    return arg


def code_args(s):
    out = []
    i = 0
    key = r'\code{'
    while True:
        j = s.find(key, i)
        if j < 0:
            out.append(s[i:])
            break
        out.append(s[i:j + len(key)])
        k = j + len(key)
        d = 1
        while d:
            c = s[k]
            if c == '\\':
                k += 2
                continue
            if c == '{':
                d += 1
            elif c == '}':
                d -= 1
            k += 1
        out.append(hl(s[j + len(key):k - 1]) + '}')
        i = k
    return ''.join(out)


head, body = t.split(r'\begin{document}', 1)
body = code_args(body)
body = body.replace(r'\status{conj.', r'\statusc{conj.').replace(r'\status{observed', r'\statuso{observed')
body = re.sub(r'\\textsc\{', r'\\rn{', body)
t = head + r'\begin{document}' + body

# ---- keywords of the logic, by role
rep(r'\newcommand{\bx}[1]{\Box_{#1}}', r'\newcommand{\bx}[1]{{\color{boxc}\Box}_{#1}}')
rep(r'\newcommand{\sep}{\mathrel{\#}}', r'\newcommand{\sep}{\mathrel{\textcolor{asrc}{\#}}}')
for n in ['keep', 'init', 'grow', 'any']:
    rep(r'\newcommand{\%s}{\kw{%s}}' % (n, n), r'\newcommand{\%s}{\chg{%s}}' % (n, n))
for n in ['rigid', 'fresh', 'old', 'dense', 'every', 'apart']:
    rep(r'\newcommand{\%s}{\kw{%s}}' % (n, n), r'\newcommand{\%s}{\asr{%s}}' % (n, n))
rep(r'\newcommand{\val}{\kw{all\text{-}values}}', r'\newcommand{\val}{\reg{all\text{-}values}}')
rep(r'\newcommand{\st}{\kw{all\text{-}stores}}', r'\newcommand{\st}{\reg{all\text{-}stores}}')
for n, w in [('fld', 'fields'), ('cel', 'cells'), ('elt', 'elements')]:
    rep(r'\newcommand{\%s}{\kw{all\text{-}%s}}' % (n, w), r'\newcommand{\%s}{\reg{all\text{-}%s}}' % (n, w))
for n, w in [('slen', 'strLength'), ('rowt', 'table'), ('esum', 'sum')]:
    rep(r'\newcommand{\%s}{\kw{%s}}' % (n, w), r'\newcommand{\%s}{\asr{%s}}' % (n, w))
t = t.replace(r'\kw{scalar}', r'\chg{scalar}').replace(r'\kw{store}', r'\reg{store}').replace(r'\kw{view}', r'\asr{view}')
rep(r'\newcommand{\code}[1]{\texttt{#1}}', r'\newcommand{\code}[1]{\textcolor{codec}{\texttt{#1}}}')
rep(r'\newcommand{\lean}[1]{\texttt{\small #1}}', r'\newcommand{\lean}[1]{\textcolor{leanc}{\texttt{\small #1}}}')
rep(r'\newcommand{\status}[1]{\textsf{\small[#1]}}',
    r'''\newcommand{\status}[1]{{\sffamily\small\textcolor{leanc}{[#1]}}}
\newcommand{\statusc}[1]{{\sffamily\small\textcolor{conjc}{[#1]}}}
\newcommand{\statuso}[1]{{\sffamily\small\textcolor{accent}{[#1]}}}''')

rep(r'\usepackage{tikz}', r'''\usepackage{tikz}
\usepackage[most]{tcolorbox}
\usepackage{titlesec}
\definecolor{accent}{HTML}{1F5F8B}
\definecolor{chgc}{HTML}{0B7A68}
\definecolor{regc}{HTML}{B45309}
\definecolor{asrc}{HTML}{6D3FC4}
\definecolor{boxc}{HTML}{C2185B}
\definecolor{rulec}{HTML}{8A1C4A}
\definecolor{codec}{HTML}{24292F}
\definecolor{ckc}{HTML}{0550AE}
\definecolor{csc}{HTML}{116329}
\definecolor{cnc}{HTML}{953800}
\definecolor{ccmc}{HTML}{6E7781}
\definecolor{leanc}{HTML}{2F6F5E}
\definecolor{conjc}{HTML}{9A6700}
\definecolor{thmbg}{HTML}{EEF4F9}
\definecolor{defbg}{HTML}{EEF6F1}
\definecolor{exbg}{HTML}{F6F4EE}
\definecolor{valc}{HTML}{1F5F8B}
\definecolor{storec}{HTML}{B45309}
\newcommand{\chg}[1]{\textcolor{chgc}{\mathsf{#1}}}
\newcommand{\reg}[1]{\textcolor{regc}{\mathsf{#1}}}
\newcommand{\asr}[1]{\textcolor{asrc}{\mathsf{#1}}}
\newcommand{\rn}[1]{\textcolor{rulec}{\textsc{#1}}}
\newcommand{\ck}[1]{\textcolor{ckc}{\textbf{#1}}}
\newcommand{\cs}[1]{\textcolor{csc}{#1}}
\newcommand{\cn}[1]{\textcolor{cnc}{#1}}
\newcommand{\cann}[1]{\textcolor{asrc}{#1}}
\newcommand{\ccm}[1]{\textcolor{ccmc}{#1}}
\titleformat*{\section}{\Large\bfseries\sffamily\color{accent}}
\titleformat{\paragraph}[runin]{\normalsize\bfseries\sffamily\color{accent}}{}{0pt}{}
\setlist[description]{font=\normalfont\sffamily\bfseries\color{accent}}
\renewcommand{\TirNameStyle}[1]{\textcolor{rulec}{\textsc{#1}}}
\newcommand{\tfbox}[2]{\tcolorboxenvironment{#1}{enhanced,breakable,colback=#2,colframe=#2,boxrule=0pt,frame hidden,
  borderline west={2.5pt}{0pt}{accent},sharp corners,left=9pt,right=6pt,top=3pt,bottom=3pt,before skip=6pt,after skip=6pt}}''')
rep(r'\usepackage[colorlinks,linkcolor=black,citecolor=black,urlcolor=black]{hyperref}',
    r'\usepackage[colorlinks,linkcolor=accent,citecolor=accent,urlcolor=accent]{hyperref}')
rep(r'''\newtheorem{remark}[theorem]{Remark}''', r'''\newtheorem{remark}[theorem]{Remark}
\tfbox{theorem}{thmbg}\tfbox{proposition}{thmbg}\tfbox{definition}{defbg}\tfbox{example}{exbg}\tfbox{remark}{exbg}''')
rep(r'\title{Tolerant frames II\\[2pt]\large What the bound proofs of a text-layout library need}',
    r'\title{\sffamily\bfseries\color{accent}Tolerant frames II\\[2pt]\large\normalfont\color{black} What the bound proofs of a text-layout library need}')

open('note-color.tex', 'w').write(t)
print('ok')
