"""Run immutable worker sources with scratch I/O isolated for independent audit.
Only /tmp/level25_cusp_aux_prime7* paths are redirected. Source mathematics
and execution order are unchanged. All source reads and output hashes are saved.
"""
from pathlib import Path
import hashlib,json,sys,time,signal
signal.alarm(300)
stage=sys.argv[1];eta=int(sys.argv[2]);assert eta in (-1,1)
names={'sourcefree':'level25_cusp_aux_prime7_symbolic.py','firstjet':'level25_cusp_aux_prime7_firstjet.py','jetrank':'level25_cusp_aux_prime7_jetrank.py','jetideals':'level25_cusp_aux_prime7_jetideals.py'}
source=Path(__file__).resolve().parent/names[stage]
read0=Path.read_text;write0=Path.write_text;sources={};outputs={}
def mapped(p):
 s=str(p)
 return Path(s.replace('/tmp/level25_cusp_aux_prime7','/tmp/level25_zero2_independent_prime7',1)) if s.startswith('/tmp/level25_cusp_aux_prime7') else p
def rd(p,*args,**kwargs):
 actual=mapped(p)
 if actual.suffix=='.py' and 'small_levels' in str(actual):sources[str(actual)]=hashlib.sha256(actual.read_bytes()).hexdigest()
 return read0(actual,*args,**kwargs)
def wr(p,data,*args,**kwargs):
 actual=mapped(p);result=write0(actual,data,*args,**kwargs)
 outputs[str(actual)]=hashlib.sha256(actual.read_bytes()).hexdigest();return result
Path.read_text=rd;Path.write_text=wr
sys.argv=[str(source),str(eta),'zero2']+(['old150'] if stage=='sourcefree' else []);start=time.monotonic();status='FAIL'
try:
 code=source.read_text();exec(compile(code,str(source),'exec'),{'__file__':str(source),'__name__':'__main__'})
 status='PASS'
finally:
 Path.read_text=read0;Path.write_text=write0
 result={'stage':stage,'eta':eta,'status':status,'elapsed_seconds':time.monotonic()-start,'sources':sources,'outputs':outputs}
 target=Path('/tmp/level25_zero2_independent_'+stage+'_'+str(eta)+'_audit.json')
 target.write_text(json.dumps(result,indent=2));print('INDEPENDENT_AUDIT',status,target,flush=True)
