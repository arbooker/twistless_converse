"""Collect complete independent Q1050 second-chart reconstruction evidence."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import hashlib,json,datetime
base=Path(__file__).resolve().parent
def sha(p):return source_sha256(p)
def readjson(p):return json.loads(Path(p).read_text().replace('\\\n',''))
sources={};runs=[];batches=[];comparisons=[]
for sign,stages in [('plus',['export','checkpoint','syzygy','even','certificate','roots']),('minus',['export','checkpoint','syzygy','polyload','negative2'])]:
 for stage in stages:
  p=Path('/tmp/level25_secondcharts_independent_'+sign+'_'+stage+'_audit.json');d=readjson(p);assert d['status']=='PASS'
  for n,h in d['sources'].items():
   assert sha(n)==h,('changed source',n)
   assert n not in sources or sources[n]==h
   sources[n]=h
  for n,h in d['inputs'].items():assert sha(n)==h,('changed input',n)
  for n,h in d['outputs'].items():assert sha(n)==h,('changed output',n)
  runs.append(d)
  if stage=='export':
   p=Path('/tmp/level25_secondcharts_independent_'+sign+'_export.log');log=p.read_text();eta=1 if sign=='plus' else -1
   assert f'EXACT_ALL_PARAMETER_SOURCE_FREE_KERNEL_VERIFIED {eta} 68' in log
 roots=Path('/tmp/level25_secondcharts_independent_plus_roots.log')
 assert 'PASS: eight disjoint rational Rouché disks' in roots.read_text()
for name,marker in [
 ('plus_poles_nonzero2_checkpoint','REDUCED_TABLES_SAVED 400 404'),
 ('plus_poles_primitive','PRIMITIVE_GERM_ROWS 400 CONSTRAINTS 801'),
 ('plus_poles_chart2_certificate','PASS_EXACT_POSITIVE_CHART2_ALGEBRA'),
 ('cusp_aux_minus_nonzero2_checkpoint','REDUCED_TABLES_SAVED 439'),
 ('cusp_aux_minus_primitive_poly','PRIMITIVE_GERM_ROWS 439'),
 ('plus_poles_negative2_even2_rational_full','PASS_EXACT_NEGATIVE_CHART2_UNIT_IDEAL')]:
 p=Path('/tmp/level25_secondcharts_independent_'+name+'_native.json');d=readjson(p);c=readjson(d['completion']);assert c['completed'] and c['status']=='PASS' and c['returncode']==0
 assert sha(c['source'])==c['source_sha256'] and sha(d['batch'])==d['batch_sha256']
 log=Path(d['log']).read_text();assert marker in log and 'INDEPENDENT_BATCH_PASS' in log
 assert 'Runtime error' not in log and 'Assertion failed' not in log
 batches.append({'input':c,'native':d,'log_sha256':sha(d['log']),'verified_marker':marker})
for stem in ['plus_poles_reduced.m','plus_poles_seed0_chart2.txt','cusp_aux_minus_reduced.m','cusp_aux_minus_seed0_chart2.txt']:
 fresh=Path('/tmp/level25_secondcharts_independent_'+stem);old=Path('/tmp/level25_'+stem)
 assert fresh.read_bytes()==old.read_bytes(),('worker table mismatch',stem)
 comparisons.append({'name':stem,'byte_identical':True,'sha256':sha(fresh)})
proofs=['level25_plus_poles_chart2.tex','level25_plus_poles_negative2.tex','level25_secondcharts_independent_audit.tex']
result={'status':'PASS_BOTH_SECOND_CHARTS_FROM_ORIGINAL_SOURCE','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Fricke signs plus/minus, lambda2 nonzero, second projective charts only. No first-chart conclusion. Level25 target M_k.','source_hashes':{Path(n).name:h for n,h in sources.items()},'audit_source_hashes':{p.name:sha(p) for p in [base/'level25_secondcharts_independent_run.py',base/'level25_secondcharts_independent_native.py',Path(__file__)]},'runs':runs,'native_batches':batches,'worker_table_comparisons':comparisons,'proof_hashes':{p:sha(base/p) for p in proofs},'root_exclusion_log_sha256':sha(roots)}
p=base/'level25_secondcharts_independent_manifest.json';result['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(result,indent=2)+'\n');print('PASS_BOTH_SECOND_CHARTS',sha(p))
