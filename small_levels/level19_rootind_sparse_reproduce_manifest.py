"""Record a completed clean-source generation and exact21 comparison."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import sys,json,hashlib,datetime
run=Path(sys.argv[1]).resolve();here=Path(__file__).resolve().parent
def sha(p):return source_sha256(p)
def read(p):return json.loads(Path(p).read_text().replace('\\\n',''))
prepared=read(run/'compare.prepared.json')
for n,h in prepared['source_record']['sources'].items():assert sha(here/n)==h
assert sha(run/'produce.m')==prepared['source_record']['batch_sha256']
assert sha(run/'compare.m')==prepared['comparison_batch_sha256']
assert sha(run/'inputs21.m')==prepared['fresh21_sha256']
assert sha(here/'level19_sparse_poles_final_data.m')==prepared['persistent21_sha256']
assert read(run/'native.completion.json')=={'completed':True,'status':'PASS_CLEAN21'}
assert read(run/'compare.completion.json')=={'completed':True,'status':'PASS_MATCH21'}
log=(run/'compare.log').read_text()
for i in range(1,22):assert f'PASS_LITERAL_EQUATION {i}\n' in log
result=dict(prepared,status='PASS_CLEAN_SOURCE_TO_ALL21_IDENTICAL_PERSISTENT_EQUATIONS',
 checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 logs={p:sha(run/p) for p in ['source.log','native.log','compare.log']},
 audit_sources={p:sha(here/p) for p in ['level19_rootind_sparse_reproduce.py',
 'level19_rootind_sparse_reproduce_verify.py','level19_rootind_sparse_reproduce_manifest.py',
 'level19_rootind_sparse_reproduce.tex']})
p=here/'level19_rootind_sparse_reproduce_manifest.json'
result['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(result,indent=2)+'\n');print(result['status'],sha(p))
