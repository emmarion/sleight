import re, sys
src = open(sys.argv[1]).read()
body = src[src.index('\n## '):]
front = """---
marp: true
theme: default
paginate: true
size: 16:9
style: |
  section { font-size: 30px; padding: 44px 60px; place-content: start !important; }
  section h2 { font-size: 42px; margin: 0 0 0.4em 0; color: #1c5cab; }
  section.lead { display: flex !important; flex-direction: column; justify-content: center !important; }
  section.lead h1 { font-size: 60px; }
  section.divider { display: flex !important; flex-direction: column; justify-content: center !important; text-align: center; }
  section.divider h1 { font-size: 54px; color: #1c5cab; }
  pre { font-size: 17px; line-height: 1.3; }
  code { font-size: 0.9em; }
  table { font-size: 24px; }
  blockquote { font-size: 30px; }
  img { display: block; margin: 0 auto; max-width: 100%; max-height: 560px; }
  li { margin: 0.25em 0; }
  section.compare table { font-size: 19px; }
  section.compare p, section.compare li { font-size: 22px; }
  section.split { display: grid !important; grid-template-columns: 1.4fr 1fr; grid-template-rows: auto 1fr; column-gap: 40px; align-items: start; }
  section.split h2 { grid-column: 1 / 3; }
  section.taskfile { padding: 24px 32px; }
  section.taskfile h2 { font-size: 30px; margin-bottom: 0.2em; }
  section.taskfile pre { font-size: 11px; line-height: 1.2; white-space: pre-wrap; column-count: 2; column-gap: 24px; margin: 0; }
  section.taskfile pre code { white-space: pre-wrap; overflow-wrap: anywhere; }
---

<!-- _class: lead -->
<!-- _paginate: false -->

# Sleight: A Language for LLMs

Eric Marion · October 14, 2026
github.com/emmarion/sleight · Apache-2.0
Code: doi.org/10.5281/zenodo.23361871
Slides: doi.org/10.5281/zenodo.23367392

- **Sleight**: a dependently typed language whose proofs erase, built for LLMs to write
- **An agent runner**: tests whether models can write Sleight, and where they get stuck
"""
out = [front]
for part in re.split(r'^(?=# |## )', body, flags=re.M):
    part = part.strip('\n').rstrip('-').strip('\n')
    if not part: continue
    if part.startswith('# '):
        out.append(f"---\n\n<!-- _class: divider -->\n\n# {part.splitlines()[0][2:].strip()}\n"); continue
    lines = part.splitlines()
    head = re.sub(r'^## ([AB]?\d+)\. ', '', lines[0])
    if head == 'Title': continue
    rest = '\n'.join(lines[1:]).strip('\n')
    keep, notes = [], []
    for para in re.split(r'\n\n', rest):
        (notes.append(para[6:].strip()) if para.startswith('Notes:') else keep.append(para))
    rest = '\n\n'.join(keep).replace('](chart/', '](../chart/')
    slide = f"## {head}\n\n{rest}\n"
    if notes: slide += "\n<!--\n" + "\n\n".join(notes).replace('-->', '- >') + "\n-->\n"
    out.append("---\n\n" + slide)
open(sys.argv[2], 'w').write('\n'.join(out))
print(len(out), 'slides')
