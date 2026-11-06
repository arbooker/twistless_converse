"""Prepare an exact comparison of clean-produced21 with persistent final data.

Usage: python3 -B this_file.py /tmp/level19_rootind_sparse_reproduce_RUN
This verification is separate from the clean producer and does not compute GB.
"""
from pathlib import Path
import sys,json,hashlib
run=Path(sys.argv[1]).resolve();here=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
rec=json.loads((run/'native.completion.json').read_text().replace('\\\n',''))
assert rec['completed'] and rec['status']=='PASS_CLEAN21'
inputs=run/'inputs21.m';saved=here/'level19_sparse_poles_final_data.m'
prefix='SetOutputFile('+json.dumps(str(run/'compare.log'))+':Overwrite:=true);SetQuitOnError(true);SetNthreads(1);SetMemoryLimit(500000000);Alarm(30);\n'
body=inputs.read_text()+'Fresh:=PP;\n'+saved.read_text()+r'''
assert #Fresh eq 21 and #Inputs eq 21;
for i in [1..21] do
 assert Evaluate(Fresh[i],[S.j:j in [1..5]]) eq Inputs[i];
 print "PASS_LITERAL_EQUATION",i;
end for;
print "PASS_CLEAN_SOURCE_EQUALS_PERSISTENT_FINAL21";
'''
body+='PrintFile('+json.dumps(str(run/'compare.completion.json'))+',"{\\\"completed\\\":true,\\\"status\\\":\\\"PASS_MATCH21\\\"}":Overwrite:=true);\nUnsetOutputFile();quit;\n'
# Magma strings use backslash quotation; avoid a second escaping level.
body=body.replace('\\\\\\"','\\"')
(run/'compare.m').write_text(prefix+body)
manifest={'status':'PREPARED_COMPARISON','run':str(run),'fresh21_sha256':sha(inputs),
 'persistent21_sha256':sha(saved),'source_record':json.loads((run/'source.completion.json').read_text()),
 'comparison_batch_sha256':sha(run/'compare.m')}
(run/'compare.prepared.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('magma -b -l500000000 -t1 '+str(run/'compare.m'))
