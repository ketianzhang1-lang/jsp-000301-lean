"""Read the public mathematical discussion for exact source links; execute nothing."""
from html.parser import HTMLParser
from urllib.request import urlopen, Request
from urllib.parse import urljoin
from pathlib import Path
import json

URL = 'https://www.erdosproblems.com/forum/thread/749'
class Links(HTMLParser):
    def __init__(self):
        super().__init__(); self.href = None; self.text = []; self.items = []
    def handle_starttag(self, tag, attrs):
        if tag == 'a':
            self.href = dict(attrs).get('href'); self.text = []
    def handle_data(self, data):
        if self.href: self.text.append(data)
    def handle_endtag(self, tag):
        if tag == 'a' and self.href:
            text = ''.join(self.text).strip()
            if 'pdf' in text.lower() or '.pdf' in self.href.lower():
                self.items.append({'text':text, 'url':urljoin(URL,self.href)})
            self.href = None
Path('evidence').mkdir(exist_ok=True)
try:
    req = Request(URL, headers={'User-Agent':'Lean formalization source review; public links only'})
    with urlopen(req, timeout=25) as response:
        text = response.read(2_000_000).decode('utf-8')
    parser = Links(); parser.feed(text)
    result = {'source':URL, 'links':parser.items}
except Exception as exc:
    result = {'source':URL, 'error':str(exc)}
Path('evidence/source-links.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
