import re,subprocess
head=open('head.html').read()
subprocess.run(['python3','prep.py','note.tex','note2.tex'],check=True)
r=subprocess.run(['pandoc','note2.tex','-f','latex','-t','html','--math-method=mathjax','--number-sections','-o','body.html'],capture_output=True,text=True)
print(r.stderr[:500])
src=open('note2.tex').read()
ab=re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}',src,re.S).group(1)
pre=src[:src.index(r'\title')]
open('ab.tex','w').write(pre+'\\begin{document}\n'+ab+'\n\\end{document}')
abh=subprocess.run(['pandoc','ab.tex','-f','latex','-t','html','--math-method=mathjax'],capture_output=True,text=True).stdout
rest=open('body.html').read()
items=re.findall(r'<h1 data-number="(\d+)"\s+id="([^"]+)"[^>]*>(.*?)</h1>',rest,re.S)
toc='<ul>'+''.join('<li><a href="#%s">%s</a></li>'%(i,re.sub(r'\s+',' ',t)) for n,i,t in items)+'</ul>'
rest=re.sub(r'(<table.*?</table>)',r'<div class="tablewrap">\1</div>',rest,flags=re.S)
rest=re.sub(r'(<h4[^>]*>)\s*<span\s+class="header-section-number">[\d.]+</span>\s*',r'\1',rest)
body=('<main>\n<header>\n<h1>Tolerant frames</h1>\n<p class="sub">A modal account of fact preservation without ownership</p>\n'
 '<p class="meta">TScert working note · 11 November 2026, revised 12 November</p>\n</header>\n<section class="abstract">'+abh+'</section>\n'
 '<details class="toc"><summary>Contents</summary>'+toc+'</details>\n'+rest+'\n</main>\n')
ABBR=('e.g','i.e','cf','conj','resp','vs','etc','Fig','Sec','Prop','Thm','Def','Ex')
def split(inner):
    out=[];cur='';i=0;depth=0;n=len(inner)
    while i<n:
        c=inner[i]
        if c=='<':
            j=inner.index('>',i); tag=inner[i:j+1]
            if tag.startswith('</'): depth-=1
            elif not tag.endswith('/>') and not re.match(r'<(br|img|hr)\b',tag): depth+=1
            cur+=tag;i=j+1;continue
        cur+=c
        if depth==0 and c in '.?!' and i+1<n and inner[i+1] in ' \n':
            w=re.search(r'([A-Za-z.]+)\.$',cur)
            if not (w and w.group(1).split('.')[-1] in ABBR) and not re.search(r'\b[A-Z]\.$',cur):
                out.append(cur);cur=''
        i+=1
    if cur.strip(): out.append(cur)
    return out
def repl(m):
    parts=split(m.group(2))
    if len(parts)<2: return m.group(0)
    return m.group(1)+''.join('<span class="s">'+p+'</span>' if p.strip() else p for p in parts)+m.group(3)
body=re.sub(r'(<p>)(.*?)(</p>)',repl,body,flags=re.S)
body=re.sub(r'(<dd>)(?!\s*<p>)(.*?)(</dd>)',repl,body,flags=re.S)

KW=r'const|let|var|for|while|if|else|return|function|type|readonly|null|undefined|true|false|new|typeof'
def hlcode(m):
    if m.group(1): return m.group(0)
    arg=m.group(3); keep=[]
    def stash(s):
        keep.append(s); return '\x00%d\x00'%(len(keep)-1)
    arg=re.sub(r'/\*\*.*?\*/',lambda x:stash('<span class="ccm">'+x.group(0)+'</span>'),arg)
    arg=re.sub(r'&quot;.*?&quot;|"[^"]*"',lambda x:stash('<span class="cs">'+x.group(0)+'</span>'),arg)
    arg=re.sub(r'&[#\w]+;',lambda x:stash(x.group(0)),arg)
    arg=re.sub(r'@[A-Za-z]+',lambda x:stash('<span class="cann">'+x.group(0)+'</span>'),arg)
    arg=re.sub(r'(?<![A-Za-z0-9_])('+KW+r')(?![A-Za-z0-9_])',lambda x:stash('<span class="ck">'+x.group(1)+'</span>'),arg)
    arg=re.sub(r'(?<![A-Za-z_.\d\x00])\d+(?![A-Za-z_\d\x00])',lambda x:stash('<span class="cn">'+x.group(0)+'</span>'),arg)
    for _ in range(3): arg=re.sub('\x00(\\d+)\x00',lambda x:keep[int(x.group(1))],arg)
    return m.group(2)+arg+'</code>'
body=re.sub(r'(<em>)?(<code>)(.*?)</code>',hlcode,body,flags=re.S)
body=re.sub(r'<span class="sans-serif">(\s*\[conj)',r'<span class="sans-serif conj">\1',body)
body=re.sub(r'<p>(?:<span class="s">)?\s*FIGUREHEAPMARKER\s*(?:</span>)?</p>',lambda m:open('fig-heap.html').read(),body)
assert 'FIGUREHEAPMARKER' not in body
open('tolerant-frames.html','w').write(head+body)
from html.parser import HTMLParser
class P(HTMLParser):
    st=[];bad=0
    def handle_starttag(self,t,a):
        if t not in('meta','link','br','img','hr','col'): self.st.append(t)
    def handle_endtag(self,t):
        if self.st and self.st[-1]==t: self.st.pop()
        else: self.bad+=1
p=P();p.feed(head+body);print('bad',p.bad,p.st,len(head+body))
