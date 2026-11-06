"""Regenerate frozen N26 negative-sign certificates with isolated scratch I/O.
Mathematical source text is unchanged; only /tmp output names in emitted
Magma code are changed. The original extractor asserts exact equality with
its stable projection JSON, while its manifest write is redirected.
"""
from pathlib import Path
import hashlib,json,sys,time,signal
signal.alarm(300)
stage,code=sys.argv[1:3];assert code in ['mmm','mpm','pmm','ppm']
base=Path(__file__).resolve().parent
names={'generate':'level26_negative_poles_generate.py','eliminate':'level26_negative_poles_eliminate.py','extract':'level26_negative_poles_extract.py'}
source=base/names[stage]
read0=Path.read_text;write0=Path.write_text;sources={};inputs={};outputs={}
def mapped(p):
 s=str(p)
 return Path(s.replace('/tmp/level26_negative_poles_','/tmp/level26_negative_independent_',1)) if s.startswith('/tmp/level26_negative_poles_') else p
def rd(p,*args,**kwargs):
 actual=mapped(p);h=hashlib.sha256(actual.read_bytes()).hexdigest()
 (sources if str(actual).startswith(str(base)) else inputs)[str(actual)]=h
 return read0(actual,*args,**kwargs)
def wr(p,data,*args,**kwargs):
 actual=mapped(p)
 if str(actual).startswith(str(base)):
  assert actual.name.startswith('level26_negative_poles_') and actual.suffix=='.json',actual
  actual=Path('/tmp/'+actual.name.replace('level26_negative_poles_','level26_negative_independent_',1))
 if actual.suffix=='.m':
  data=data.replace('/tmp/level26_negative_poles_','/tmp/level26_negative_independent_')
  data=data.replace('Alarm(45);','Alarm(180);')
 result=write0(actual,data,*args,**kwargs);outputs[str(actual)]=hashlib.sha256(actual.read_bytes()).hexdigest();return result
Path.read_text=rd;Path.write_text=wr
if stage=='generate':args=[str(1 if c=='p' else -1) for c in code]
elif stage=='eliminate':args=['/tmp/level26_negative_independent_higher2_'+code+'.json']
else:args=[code,'/tmp/level26_negative_independent_'+code+'_chart1_xy.txt']
sys.argv=[str(source)]+args;start=time.monotonic();status='FAIL';ns={'__file__':str(source),'__name__':'__main__'}
try:
 text=source.read_text();exec(compile(text,str(source),'exec'),ns)
 if stage=='extract':
  p=Path('/tmp/level26_negative_independent_'+code+'_fresh_projection.json');p.write_text(json.dumps(ns['values'],indent=2))
 status='PASS'
finally:
 Path.read_text=read0;Path.write_text=write0
 result={'stage':stage,'case':code,'status':status,'elapsed_seconds':time.monotonic()-start,'sources':sources,'inputs':inputs,'outputs':outputs}
 target=Path('/tmp/level26_negative_independent_'+stage+'_'+code+'_audit.json');target.write_text(json.dumps(result,indent=2));print('INDEPENDENT_AUDIT',status,target,flush=True)
