#!/usr/bin/env python3
"""Render ```tikz fenced blocks in Quartz content/ to SVG and replace them
with image embeds. The Obsidian vault keeps the original TikzJax blocks;
this script only rewrites the copies under content/."""
import hashlib
import re
import subprocess
import sys
import tempfile
from pathlib import Path

CONTENT = Path(__file__).resolve().parent.parent / "content"
SVG_DIR = CONTENT / "static" / "tikz"

PREAMBLE = r"""\documentclass[border=6pt]{standalone}
\usepackage{tikz}
"""

def render_svg(body: str, out: Path) -> None:
    # split off \usepackage lines and the document body
    packages = re.findall(r"\\usepackage(?:\[[^\]]*\])?\{[^}]*\}", body)
    m = re.search(r"\\begin\{document\}(.*)\\end\{document\}", body, re.S)
    inner = m.group(1).strip() if m else body.strip()
    # real LaTeX (unlike TikzJax) rejects blank lines inside tikzcd
    inner = "\n".join(l for l in inner.split("\n") if l.strip())
    doc = PREAMBLE + "\n".join(packages) + "\n\\begin{document}\n" + inner + "\n\\end{document}\n"
    with tempfile.TemporaryDirectory() as td:
        tex = Path(td) / "fig.tex"
        tex.write_text(doc)
        r = subprocess.run(["latex", "-interaction=nonstopmode", "-halt-on-error", "fig.tex"],
                           cwd=td, capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError("latex failed:\n" + r.stdout[-2000:])
        subprocess.run(["dvisvgm", "--no-fonts", "--exact", "fig.dvi", "-o", str(out)],
                       cwd=td, check=True, capture_output=True, text=True)

def main() -> None:
    SVG_DIR.mkdir(parents=True, exist_ok=True)
    pat = re.compile(r"```tikz\n(.*?)```", re.S)
    for md in sorted(CONTENT.rglob("*.md")):
        text = md.read_text()
        changed = False
        def repl(m: re.Match) -> str:
            nonlocal changed
            body = m.group(1)
            name = "tikz-" + hashlib.sha1(body.encode()).hexdigest()[:10] + ".svg"
            svg = SVG_DIR / name
            if not svg.exists():
                print(f"rendering {name} for {md.name}")
                render_svg(body, svg)
            changed = True
            return f"![](static/tikz/{name})"
        new = pat.sub(repl, text)
        if changed:
            md.write_text(new)
            print(f"updated {md.name}")

if __name__ == "__main__":
    sys.exit(main())
