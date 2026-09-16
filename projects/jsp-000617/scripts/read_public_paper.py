"""Download the author's publicly linked PDF for source review only; execute nothing."""
from pathlib import Path
from urllib.request import Request,urlopen
import hashlib,json
Path('evidence').mkdir(exist_ok=True)
url='https://drive.google.com/uc?export=download&id=1ygE9Gqiev9TsEsYZ1ZY5ba5ZS9mJOO6Y'
result={'url':url,'purpose':'source review; not a proof or claimed verification'}
try:
    with urlopen(Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=30) as response:
        data=response.read(10_000_001)
    if len(data)>10_000_000 or not data.startswith(b'%PDF-'):
        raise ValueError('Response is not an acceptable-size PDF')
    Path('evidence/public-source-paper.pdf').write_bytes(data)
    result.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
except Exception as exc:
    result['error']=str(exc)
Path('evidence/paper-fetch.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
