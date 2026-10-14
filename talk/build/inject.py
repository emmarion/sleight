js = """<script>window.addEventListener('load',()=>{const out=[];document.querySelectorAll('section').forEach((s,i)=>{const sb=s.getBoundingClientRect();let bottom=0;for(const k of s.children){const r=k.getBoundingClientRect();if(r.height>0)bottom=Math.max(bottom,r.bottom-sb.top);}let wide=0;s.querySelectorAll('pre,table').forEach(k=>{wide=Math.max(wide,k.scrollWidth-k.clientWidth)});const h=(s.querySelector('h1,h2')||{}).textContent||'';out.push(`${i+1}\\t${Math.round(bottom)}\\t${Math.round(sb.height)}\\t${wide}\\t${h}`)});const p=document.createElement('pre');p.id='MEASURE';p.textContent=out.join('\\n');document.body.appendChild(p);});</script>"""
import re
h=open('slides.html').read()
h=re.sub(r'<pre is="marp-pre"[^>]*>', '<pre>', h)
open('print.html','w').write(h)
open('measure.html','w').write(h.replace('</body>', js + '</body>'))
