"""Wrap an already regenerated exact Magma certificate with saved completion.

No terminal interaction is used. A missing completion is never a success.
The original certificate is unchanged except extra assertions and logging.
"""
from pathlib import Path
import sys,json,hashlib
code=sys.argv[1];assert code in ['mmm','mpm','pmm','ppm']
prefix='/tmp/level26_negative_independent_'+code
p=Path(prefix+'.m');s=p.read_text()
assert 'SetGBGlobalModular(false);' in s
assert s.count('GlobalModular:=false')==2
assert s.endswith('quit;\n')
s=s[:-6]
s=s.replace('for chart in [1..2] do','chart2unit:=false;\nfor chart in [1..2] do')
s=s.replace('then print "UNIT",chart;continue;','then if chart eq 2 then chart2unit:=true;end if;print "UNIT",chart;continue;')
s+='\nassert chart2unit;\nassert not GetGBGlobalModular();\n'
done=prefix+'_exact_completion.json';log=prefix+'_exact_batch.log'
out='SetOutputFile('+json.dumps(log)+':Overwrite:=true);\ntry\n'+s
out+='PrintFile('+json.dumps(done)+','+json.dumps(json.dumps({'status':'PASS','case':code,'global_modular':False,'exit_status':0}))+':Overwrite:=true);\n'
out+='print "INDEPENDENT_EXACT_BATCH_PASS '+code+'";\ncatch e\nprint e;\n'
out+='PrintFile('+json.dumps(done)+','+json.dumps(json.dumps({'status':'FAIL','case':code,'exit_status':1}))+':Overwrite:=true);\nend try;\nquit;\n'
target=Path(prefix+'_exact_batch.m');target.write_text(out)
Path(prefix+'_exact_batch_source.json').write_text(json.dumps({'original_input_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'batch_source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
print(target)
