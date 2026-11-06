"""Fresh negative first-chart normalization and exact Cramer reduction.

Reads this auditor's independently regenerated all439-syzygy chart dump.
The selected100 expressions are taken from the fresh rational input itself;
the older finite-field diagnostic file is not used as mathematical evidence.
"""
from pathlib import Path
import sys,json,hashlib,time,signal,re
signal.alarm(240)
stage=sys.argv[1];base=Path(__file__).resolve().parent
names={'normalize':'level25_cusp_aux_minus_even_prepare.py','reduce':'level25_plus_poles_negative1_generic_audit_prepare.py','strata':'level25_plus_poles_negative1_strata_certificate.py','dzero':'level25_plus_poles_negative1_dzero_certificate.py'}
source=base/names[stage];args=['1','pure'] if stage=='normalize' else []
fresh='/tmp/level25_secondcharts_independent_cusp_aux_minus_even1_rational_pure.m'
def mapped(s):
 if s in ['/tmp/level25_root_negative_first_even1_rational_pure.m','/tmp/level25_cusp_aux_minus_even1_finite_pure.m']:return fresh
 return s.replace('/tmp/level25_cusp_aux','/tmp/level25_secondcharts_independent_cusp_aux').replace('/tmp/level25_plus_poles','/tmp/level25_secondcharts_independent_plus_poles')
read0=Path.read_text;write0=Path.write_text;sources={};inputs={};outputs={}
def rd(p,*a,**k):
 actual=Path(mapped(str(p)));h=hashlib.sha256(actual.read_bytes()).hexdigest()
 (sources if str(actual).startswith(str(base)) else inputs)[str(actual)]=h
 return read0(actual,*a,**k)
def wr(p,data,*a,**k):
 actual=Path(mapped(str(p)));assert str(actual).startswith('/tmp/level25_secondcharts_independent_')
 if actual.suffix=='.m':data=mapped(data)
 ret=write0(actual,data,*a,**k);outputs[str(actual)]=hashlib.sha256(actual.read_bytes()).hexdigest();return ret
Path.read_text=rd;Path.write_text=wr;sys.argv=[str(source)]+args
start=time.monotonic();status='FAIL'
try:
 text=source.read_text();exec(compile(text,str(source),'exec'),{'__name__':'__main__','__file__':str(source)})
 status='PASS'
finally:
 Path.read_text=read0;Path.write_text=write0
 p=Path('/tmp/level25_secondcharts_independent_negative1_'+stage+'_audit.json')
 p.write_text(json.dumps({'stage':stage,'status':status,'elapsed_seconds':time.monotonic()-start,'sources':sources,'inputs':inputs,'outputs':outputs},indent=2)+'\n')
 print('NEGATIVE1_INDEPENDENT',stage,status,flush=True)
