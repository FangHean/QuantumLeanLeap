#!/usr/bin/env python3
"""Create a reproducible, allowlisted source distribution, never caches or credentials."""
import gzip
import hashlib
import io
from pathlib import Path
import tarfile
ROOT=Path(__file__).resolve().parents[1]
VERSION='0.1.0'
FILES=['README.md','LICENSE','NOTICE','CHANGELOG.md','lakefile.toml','lake-manifest.json',
       'lean-toolchain','QuantumLeanLeap.lean','requirements.txt','.gitignore']
DIRS=['QuantumLeanLeap','scripts','bench','docs','verification','.github']
def main():
    paths=[ROOT/x for x in FILES]
    for folder in DIRS:
        paths.extend(p for p in (ROOT/folder).rglob('*') if p.is_file() and not p.is_symlink()
                     and '__pycache__' not in p.parts and p.suffix not in {'.pyc','.log'})
    out=ROOT/'dist';out.mkdir(exist_ok=True)
    target=out/f'QuantumLeanLeap-{VERSION}.tar.gz'
    buffer=io.BytesIO()
    with tarfile.open(fileobj=buffer,mode='w') as tar:
        for p in sorted(set(paths)):
            if not p.is_file(): raise FileNotFoundError(p)
            info=tar.gettarinfo(str(p),arcname=f'QuantumLeanLeap-{VERSION}/'+str(p.relative_to(ROOT)))
            info.uid=info.gid=0;info.uname=info.gname='';info.mtime=0;info.mode=0o644
            with p.open('rb') as f: tar.addfile(info,f)
    with target.open('wb') as f:
        with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(buffer.getvalue())
    digest=hashlib.sha256(target.read_bytes()).hexdigest()
    target.with_suffix(target.suffix+'.sha256').write_text(digest+'  '+target.name+'\n')
    print(target);print(digest)
if __name__=='__main__':main()
