"""Bind the independent source regeneration and exact sparse-row audit."""
from pathlib import Path
from document_provenance import source_sha256, recorded_document_provenance
import hashlib,json,datetime
here=Path(__file__).resolve().parent
def sha(p):return source_sha256(p)
record=json.loads(Path('/tmp/level19_rootind_sparse_all_prepared.json').read_text())
assert record['status']=='PASS_SOURCE_REGENERATION_NATIVE_PREPARED'
for name,digest in record['sources'].items(): assert sha(here/name)==digest
assert sha('/tmp/level19_rootind_sparse_all_native.m')==record['all15_batch_sha256']
assert sha('/tmp/level19_exact_membership_sparse_fast.m')==record['comparison_sparse_export_sha256']
assert sha('/tmp/level19_sparse_poles_compactall_fast.m')==record['compact_old_input_sha256']
marker=Path('/tmp/level19_rootind_sparse_all_native.pass').read_text()
assert marker.strip()=='PASS all15 sparse syzygies and originalSafe15 compactification'
log=Path('/tmp/level19_rootind_sparse_all_native.log').read_text()
for s in ['PASS_ALL15_PRIMITIVE_SYZYGIES_AND_EXACT_INVERSE_COMPACTIFICATION',
          'PASS_SAFE15_AND_SIX_SPARSE_FINAL_INPUT_PROVENANCE']: assert s in log
for i in range(1,16):
 assert f'PASS_SPARSE_SOURCE_ROW {i} ' in log
 assert f'PASS_SAFE15_ORIGINAL_TO_COMPACT {i} ' in log
result={'status':'PASS_SOURCE_TO_SPARSE_CONSTRAINT_NO_FINAL_GB_CLAIM',
 'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_record':record,
 'native_log_sha256':sha('/tmp/level19_rootind_sparse_all_native.log'),
 'native_pass_sha256':sha('/tmp/level19_rootind_sparse_all_native.pass'),
 'scope':'Equal-sign generic stratum; all15 sparse polynomial primitive syzygies and exact compactification; fresh originalSafe15 versus oldcompact first15; arbitrary b and no nonzero-minor assumption.',
 'final_selected_sparse_indices':[8,11,12,13,14,15],
 'final_selected_fourth_rows':[34,40,42,44,46,54],
 'audit_sources':{name:sha(here/name) for name in [
  'level19_rootind_sparse_prepare.py','level19_rootind_sparse_all_prepare.py','level19_rootind_sparse_audit.tex',
  'level19_rootind_sparse_manifest.py']}}
p=here/'level19_rootind_sparse_manifest.json'
result['document_hash_provenance'] = recorded_document_provenance(); p.write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],sha(p))
