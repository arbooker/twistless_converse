"""Final generic negative first-chart source/reduction/transfer audit."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import hashlib,json,datetime
base=Path(__file__).resolve().parent
def sha(p):return source_sha256(p)
def rd(p):return json.loads(Path(p).read_text().replace('\\\n',''))
prior=base/'level25_secondcharts_independent_manifest.json';prior_positive=base/'level25_secondcharts_independent_positive1_manifest.json'
old=rd(prior);assert old['status']=='PASS_BOTH_SECOND_CHARTS_FROM_ORIGINAL_SOURCE'
assert rd(prior_positive)['status']=='PASS_POSITIVE_FIRST_CHART_FROM_ORIGINAL_Q1050_SOURCE'
for n,h in old['source_hashes'].items():assert sha(base/n)==h,n
runs=[]
for stage in ['normalize','reduce']:
 d=rd('/tmp/level25_secondcharts_independent_negative1_'+stage+'_audit.json');assert d['status']=='PASS'
 for group in ['sources','inputs','outputs']:
  for p,h in d[group].items():assert sha(p)==h,(group,p)
 runs.append(d)
lit=rd('/tmp/level25_secondcharts_independent_negative1_transfer_input_audit.json')
assert lit['status']=='PASS_LITERAL_INPUT_PROVENANCE' and lit['negative14_literal_equality'] and lit['positive15_literal_equality']
assert sha(base/'level25_plus_poles_negative1_generic_audit_transfer.m')==lit['transfer_source_sha256']
assert sha('/tmp/level25_secondcharts_independent_plus_poles_negative1_generic_audit_relations.txt')==lit['fresh14_sha256']
assert sha(base/'level25_plus_poles_chart1_rows.json')==lit['positive15_sha256']
batches=[]
for name,markers in [('plus_poles_negative1_generic_audit_export',['PASS_INDEPENDENT_INPUT_AND_CRAMER','PASS_INDEPENDENT_GENERIC_RELATIONS 14']),('negative1_transfer',['NOSAT_GB 35','PASS_U_NONZERO_FROM_S_SQUARED','PASS_NEGATIVE_TO_POSITIVE_ALL15']+[f'PASS_TRANSFER_ROW {i}\n' for i in range(1,16)])]:
 d=rd('/tmp/level25_secondcharts_independent_'+name+'_native.json');c=rd(d['completion'])
 assert c['completed'] and c['status']=='PASS' and c['returncode']==0
 assert sha(c['source'])==c['source_sha256'] and sha(d['batch'])==d['batch_sha256']
 log=Path(d['log']).read_text();assert all(m in log for m in markers)
 assert 'Assertion failed' not in log and 'Runtime error' not in log
 batches.append({'native':d,'completion':c,'log_sha256':sha(d['log']),'verified_markers':markers})
partial=base/'level25_root_negative_first_partial_audit.json';pr=rd(partial)
assert pr['status']=='PASS_NEGATIVE_FIRST_CHART_EXCEPT_GENERIC_NONZERO_DENOMINATOR'
for p,h in pr['proof_hashes'].items():assert sha(base/p)==h,p
proofs=['level25_plus_poles_negative1_generic_audit.tex','level25_secondcharts_independent_negative1_audit.tex']
auditfiles=['level25_secondcharts_independent_negative1_run.py','level25_secondcharts_independent_negative1_transfer.py','level25_secondcharts_independent_negative1_manifest.py']
out={'status':'PASS_FINAL_NEGATIVE_FIRST_CHART_GENERIC_TRANSFER','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'claim':'Fresh original-source chain yields the exact14 relations; Uzero excluded by S squared; all15 positive obstruction rows transfer directly with nonvanishing denominators. Positive saturation extends by t=1/(AXY), preserving physical X,Y. Exceptional negative strata use separately audited root manifest. Level25 target M_k.','prior_source_chain_manifest_sha256':sha(prior),'prior_positive_firstchart_manifest_sha256':sha(prior_positive),'exceptional_strata_manifest_sha256':sha(partial),'runs':runs,'literal_input_comparison':lit,'native_batches':batches,'proof_hashes':{p:sha(base/p) for p in proofs},'audit_source_hashes':{p:sha(base/p) for p in auditfiles}}
p=base/'level25_secondcharts_independent_negative1_manifest.json';out['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(out,indent=2)+'\n');print('PASS_FINAL_NEGATIVE_GENERIC_TRANSFER',sha(p))
