"""Assemble the independent rebuild audit after every bounded run passes."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import json,hashlib,re,datetime
base=Path(__file__).resolve().parent
sources={};runs=[]
for eta in [1,-1]:
 for stage in ['firstjet','jetrank','jetideals','sourcefree']:
  p=Path('/tmp/level25_zero2_independent_'+stage+'_'+str(eta)+'_audit.json')
  r=json.loads(p.read_text());assert r['status']=='PASS'
  for name,h in r['sources'].items():
   assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h,('source changed',name)
   if name in sources:assert sources[name]==h
   sources[name]=h
  for name,h in r['outputs'].items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h
  log=Path('/tmp/level25_zero2_independent_'+stage+'_'+str(eta)+'.log')
  text=log.read_text()
  if stage=='sourcefree':assert 'EXACT_ALL_PARAMETER_SOURCE_FREE_KERNEL_VERIFIED '+str(eta)+' 68' in text
  if stage=='firstjet':
   assert ('LEADING 1 1047 [294, 630, 672] 530 2941' if eta==1 else 'LEADING -1 1046 [420, 714, 840, 882] 541 2931') in text
   assert ('CONSTRAINTS 540' if eta==1 else 'CONSTRAINTS 852') in text
  if stage=='jetrank':assert ('UNIQUE 95' if eta==1 else 'UNIQUE 68') in text
  runs.append({'stage':stage,'eta':eta,'status':'PASS','elapsed_seconds':r['elapsed_seconds'],'log_path':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'outputs':r['outputs']})
comparisons=[]
for eta in [1,-1]:
 p=Path('/tmp/level25_zero2_independent_compare_'+str(eta)+'.json');r=json.loads(p.read_text());assert all(c['polynomial_list_match'] for c in r['charts'])
 ref=base/Path(r['reference']).name;assert hashlib.sha256(ref.read_bytes()).hexdigest()==r['reference_sha256']
 comparisons.append(r)
magmalog=Path('/tmp/level25_zero2_independent_all_charts_pass.log');txt=magmalog.read_text()
for eta in [1,-1]:
 for chart in [0,1]:assert 'INDEPENDENT_ZERO2_'+str(eta)+'_CHART_'+str(chart)+'_PASS' in txt
proofs=['level25_cusp_aux_zero2_plus.tex','level25_cusp_aux_zero2_minus.tex','level25_cusp_aux_prime7_quotient.tex','level25_finish_eta_plus_cusp_poles.tex','level25_finish_eta_minus_cusp_poles.tex','level25_zero2_independent_audit.tex']
out={'status':'PASS','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'claim':'Both eta signs with lambda2=0: original Q1050 specialized source-free quotient and full leading/first-source chart certificates independently rebuilt; only possible simple poles at s=k, using separately established old150 first-source denominator-five identities.','source_hashes':{Path(p).name:h for p,h in sources.items()},'audit_source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [base/'level25_zero2_independent_run.py',base/'level25_zero2_independent_compare.py',base/'level25_zero2_independent_manifest.py']},'proof_hashes':{p:source_sha256(base/p) for p in proofs},'runs':runs,'chart_comparisons':comparisons,'magma':{'status':'PASS_ALL_FOUR_UNIT_IDEALS','command':'magma /tmp/level25_zero2_independent_all_charts.m','source_sha256':hashlib.sha256(Path('/tmp/level25_zero2_independent_all_charts.m').read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(magmalog.read_bytes()).hexdigest(),'output_path':str(magmalog)}}
p=base/'level25_zero2_independent_manifest.json';out['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(out,indent=2));print('PASS: independent zero-lambda2 audit, both signs, all source hashes unchanged');print(p)
