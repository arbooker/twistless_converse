"""Prepare a native bounded Magma batch with unique completion record."""
from pathlib import Path
import sys,json,hashlib,datetime
p=Path(sys.argv[1]);assert str(p).startswith('/tmp/level25_secondcharts_independent_')
s=p.read_text();assert 'quit;' in s
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
stem=str(p.with_suffix(''))+'_'+stamp
record={'source':str(p),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'completed':False,'status':'running'}
completion=stem+'.completion.json';log=stem+'.log'
head='SetOutputFile('+json.dumps(log)+':Overwrite:=true);\nSetQuitOnError(true); SetGBGlobalModular(false); SetMemoryLimit(500000000); SetNthreads(1);\n'
head+='PrintFile('+json.dumps(completion)+','+json.dumps(json.dumps(record))+':Overwrite:=true);\n'
record.update(completed=True,status='PASS',returncode=0)
finish='assert not GetGBGlobalModular();\nPrintFile('+json.dumps(completion)+','+json.dumps(json.dumps(record))+':Overwrite:=true);\nprint "INDEPENDENT_BATCH_PASS";\nquit;'
s=s.replace('Alarm(45);','Alarm(180);').replace('Alarm(150);','Alarm(180);').replace('quit;',finish)
batch=Path(stem+'.m');batch.write_text(head+s)
out={'command':'magma -b -l500000000 -t1 '+str(batch),'completion':completion,'log':log,'batch':str(batch),'batch_sha256':hashlib.sha256(batch.read_bytes()).hexdigest()}
Path(str(p.with_suffix(''))+'_native.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
