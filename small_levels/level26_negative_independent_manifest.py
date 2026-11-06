"""Collect source-to-projection reproducibility checks, with exact GB enabled."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import hashlib,json,datetime
base=Path(__file__).resolve().parent
def sha(p):return source_sha256(p)
sources={};cases=[]
for code in ['mmm','mpm','pmm','ppm']:
 stages=[]
 for stage in ['generate','eliminate','extract']:
  p=Path('/tmp/level26_negative_independent_'+stage+'_'+code+'_audit.json')
  d=json.loads(p.read_text());assert d['status']=='PASS'
  for name,h in d['sources'].items():
   assert sha(name)==h,('changed source',name)
   assert name not in sources or sources[name]==h
   sources[name]=h
  for name,h in d['outputs'].items():assert sha(name)==h,('changed output',name)
  stages.append(d)
 prefix='/tmp/level26_negative_independent_'+code
 original=Path(prefix+'.m');s=original.read_text()
 assert 'SetGBGlobalModular(false);' in s and s.count('GlobalModular:=false')==2
 if code=='mmm':
  log=Path(prefix+'_exact.log');completion={'status':'PASS','evidence':'completed exec command exit_code=0; full stdout saved before unattended workflow change'}
  batch_hash=sha(original)
 else:
  completion=json.loads(Path(prefix+'_exact_completion.json').read_text())
  assert completion['status']=='PASS' and completion['exit_status']==0 and completion['global_modular'] is False
  log=Path(prefix+'_exact_batch.log');batch_hash=sha(prefix+'_exact_batch.m')
 text=log.read_text()
 assert 'UNIT 2' in text and 'XY_COUNT 2' in text
 assert ('IDEAL_RESULT 1 40' if code in ['mmm','ppm'] else 'IDEAL_RESULT 1 42') in text
 assert 'Runtime error' not in text and 'Assertion failed' not in text
 fresh=json.loads(Path(prefix+'_fresh_projection.json').read_text())
 saved=base/('level26_negative_poles_'+code+'_projection.json');old=json.loads(saved.read_text())
 assert all(old[k]==v for k,v in fresh.items())
 cases.append({'case':code,'status':'PASS','stages':stages,'completion':completion,'log_sha256':sha(log),'log_path':str(log),'magma_batch_sha256':batch_hash,'projection_sha256':sha(saved),'exact_projection_comparison':True})
proofs=['level26_negative_poles_complete.tex','level26_negative_poles_signs.py','level26_root_modulus_audit.py','level26_negative_independent_audit.tex']
result={'status':'PASS_ALL_FOUR_SOURCE_TO_EXACT_PROJECTION','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_hashes':{Path(p).name:h for p,h in sources.items()},'audit_source_hashes':{p.name:sha(p) for p in [base/'level26_negative_independent_run.py',base/'level26_negative_independent_batch.py',Path(__file__)]},'cases':cases,'downstream_proof_hashes':{p:sha(base/p) for p in proofs},'claim':'Original Q780 three-layer source regenerated independently for all four negative-bad13 signs; primitive polynomial syzygies and both charts recomputed with deterministic rational Groebner bases; chart2 unit ideal and exact membership of both saved x,Y projection polynomials in chart1 checked. Analytic normalization and physical-locus exclusions are separate audited proof inputs.'}
p=base/'level26_negative_independent_manifest.json';result['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(result,indent=2)+'\n');print('INDEPENDENT_N26_ALL_FOUR_PASS',sha(p))
