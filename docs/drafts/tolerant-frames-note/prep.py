import re,sys
src=open(sys.argv[1]).read()
def grp(s,i):
    assert s[i]=='{'
    d=0
    for j in range(i,len(s)):
        if s[j]=='{': d+=1
        elif s[j]=='}':
            d-=1
            if d==0: return s[i+1:j], j+1
    raise Exception
m=re.search(r'\\begin\{mathpar\}(.*?)\\end\{mathpar\}',src,re.S)
body=m.group(1); out=[]
for part in body.split(r'\and'):
    part=part.strip()
    mm=re.match(r'\\inferrule\*\[left=(.*?)\]',part)
    name=mm.group(1).replace('$','')
    name=re.sub(r'\^\{\+\}',r'}^{+}\\text{',name)
    a,i=grp(part,mm.end()); c,_=grp(part,i)
    a=a.replace(r'\\',r'\qquad ')
    out.append(r'\[\class{rulec}{\text{(%s)}}\quad \dfrac{%s}{%s}\]' % (name,a,c))
src=src[:m.start()]+'\n\n'.join(out)+src[m.end():]
src=re.sub(r'\\begin\{description\}\[[^\]]*\]',r'\\begin{description}',src)
src=re.sub(r'\\begin\{figure\}.*?\\end\{figure\}','FIGUREHEAPMARKER\n',src,flags=re.S)
src=src.replace(r'Figure~\ref{fig:heap}','Figure 1')
src=src.replace(r'\llbracket','⟦').replace(r'\rrbracket','⟧')

# colour by role on the page: MathJax \class, styled by the page's CSS
def swap(old,new):
    global src
    assert src.count(old)==1,old
    src=src.replace(old,new)
swap(r'\newcommand{\bx}[1]{\Box_{#1}}',r'\newcommand{\bx}[1]{\class{boxc}{\Box}_{#1}}')
swap(r'\newcommand{\sep}{\mathrel{\#}}',r'\newcommand{\sep}{\mathrel{\class{asr}{\#}}}')
for n in ['keep','init','grow','any']: swap(r'\newcommand{\%s}{\kw{%s}}'%(n,n),r'\newcommand{\%s}{\class{chg}{\mathsf{%s}}}'%(n,n))
for n in ['rigid','fresh','old','dense','every','apart']: swap(r'\newcommand{\%s}{\kw{%s}}'%(n,n),r'\newcommand{\%s}{\class{asr}{\mathsf{%s}}}'%(n,n))
swap(r'\newcommand{\val}{\kw{all\text{-}values}}',r'\newcommand{\val}{\class{reg}{\mathsf{all\text{-}values}}}')
swap(r'\newcommand{\st}{\kw{all\text{-}stores}}',r'\newcommand{\st}{\class{reg}{\mathsf{all\text{-}stores}}}')
src=src.replace(r'\kw{scalar}',r'\class{chg}{\mathsf{scalar}}').replace(r'\kw{store}',r'\class{reg}{\mathsf{store}}').replace(r'\kw{view}',r'\class{asr}{\mathsf{view}}')
swap(r'\newcommand{\lean}[1]{\texttt{\small #1}}',r'\newcommand{\lean}[1]{\emph{\texttt{#1}}}')
open(sys.argv[2],'w').write(src)
