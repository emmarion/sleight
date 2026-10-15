surface, ink, ink2, grid, gray, stripe = '#fcfcfb', '#0b0b0b', '#52514e', '#e4e3df', '#9a9893', '#f3f2ef'
hues = ['#2a78d6', '#d9730d', '#1a9a6c', '#8a4fd0']
font = "font-family='Inter, Helvetica, Arial, sans-serif'"
def text(x, y, s, size=17, fill=ink, anchor='start', extra=''):
    return f"<text x='{x}' y='{y}' {font} font-size='{size}' fill='{fill}' text-anchor='{anchor}' {extra}>{s}</text>"
def dot(x, y, fill, hollow=False):
    return f"<circle cx='{x:.1f}' cy='{y}' r='{6.5 if hollow else 8}' fill='{surface if hollow else fill}' stroke='{fill if hollow else surface}' stroke-width='{3 if hollow else 2}'/>"
def frame(W, H, title, subtitle):
    return [f"<svg xmlns='http://www.w3.org/2000/svg' width='{W}' height='{H}' viewBox='0 0 {W} {H}'>",
            f"<rect width='{W}' height='{H}' fill='{surface}'/>",
            text(40, 48, title, 30, extra="font-weight='600'"), text(40, 78, subtitle)]
def dotplot(out, labels, panels, left, top, rowh, pw, gap, value, after=None):
    n = len(labels); ybot = top + 30 + (n - 1) * rowh + rowh / 2
    for i, label in enumerate(labels):
        y = top + 30 + i * rowh
        if i % 2 == 0:
            out.append(f"<rect x='{left-8}' y='{y-rowh/2}' width='{len(panels)*pw+(len(panels)-1)*gap+16}' height='{rowh}' fill='{stripe}' opacity='0.6'/>")
        out.append(text(left - 16, y + 6, label, anchor='end'))
    for p, (title, lo, hi, ticks, fmt) in enumerate(panels):
        x0 = left + p * (pw + gap); sx = lambda v: x0 + (min(v, hi) - lo) / (hi - lo) * pw
        out.append(text(x0, top, title, 18, hues[p], extra="font-weight='600'"))
        for t in ticks:
            out.append(f"<line x1='{sx(t):.1f}' y1='{top+8}' x2='{sx(t):.1f}' y2='{ybot}' stroke='{grid}' stroke-width='1'/>")
            out.append(text(f"{sx(t):.1f}", ybot + 22, fmt(t), 14, ink2, 'middle'))
        for i in range(n):
            value(out, p, i, x0, top + 30 + i * rowh, sx, fmt)
    return ybot
