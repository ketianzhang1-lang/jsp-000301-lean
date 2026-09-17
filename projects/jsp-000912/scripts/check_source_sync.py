from pathlib import Path

root = Path(__file__).resolve().parents[1]
modules = ['Grid', 'Construction', 'Decay', 'Potential', 'Main']
standalone = (root / 'FullProof.lean').read_text()
standalone = standalone[standalone.index('import '):]
modular = '\n'.join((root / 'JSP912' / f'{name}.lean').read_text() for name in modules)

def body(text):
    return [line.strip() for line in text.splitlines()
            if line.strip() and not line.startswith('import ')]

if body(standalone) != body(modular):
    raise SystemExit('Standalone and modular proof bodies differ.')
print('PASS: standalone and five-module proof bodies agree.')
