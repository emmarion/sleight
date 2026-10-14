import re,html
d=open('dom.html').read(); m=re.search(r'<pre id="MEASURE">(.*?)</pre>',d,re.S)
rows=[l.split('\t') for l in html.unescape(m.group(1)).splitlines()]
bad=[r for r in rows if int(r[1])>int(r[2])-30 or int(r[3])>2]
print('pages',len(rows),'overflowing',len(bad))
for i,b,h,w,t in bad: print(f"  page {i}: {t[:55]} | to {b}/{h}px | wide {w}")
