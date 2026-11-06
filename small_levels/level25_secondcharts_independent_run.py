"""Independent isolated reconstruction of both nonzero-eigenvalue second charts.

The exporter additionally executes the original source-free-kernel assertions
that its ordinary truncated source execution omits. Mathematical rows unchanged.
"""
from pathlib import Path
import sys,json,hashlib,time,signal
signal.alarm(360)
stage,sign=sys.argv[1:3];assert sign in ['plus','minus']
base=Path(__file__).resolve().parent
names={'export':'level25_cusp_aux_magma_firstjet_export.py','checkpoint':'level25_plus_poles_prepare.py' if sign=='plus' else 'level25_cusp_aux_minus_prepare.py','syzygy':'level25_plus_poles_syzygy_prepare.py' if sign=='plus' else 'level25_cusp_aux_minus_syzygy_prepare.py','polyload':'level25_cusp_aux_minus_polyload_prepare.py','even':'level25_plus_poles_even_prepare.py','certificate':'level25_plus_poles_chart2_certificate.py','negative2':'level25_plus_poles_negative2_prepare.py','roots':'level25_plus_poles_chart2_roots.py'}
args={'export':['1' if sign=='plus' else '-1','nonzero2'],'checkpoint':['checkpoint'],'syzygy':['400' if sign=='plus' else '439','0','export'],'polyload':[],'even':['2','export'],'certificate':[],'negative2':['2'],'roots':[]}
names.update(even1='level25_plus_poles_even_prepare.py',certificate1='level25_plus_poles_chart1_certificate.py',modulus1='level25_root_chart1_modulus.py')
args.update(even1=['1'],certificate1=[],modulus1=[])
# Certificate adapter needs the full even input including the ideal declaration.
if stage=='even':args['even']=['2']
source=base/names[stage];read0=Path.read_text;write0=Path.write_text
sources={};inputs={};outputs={}
def transform(s):
 return s.replace('/tmp/level25_plus_poles','/tmp/level25_secondcharts_independent_plus_poles').replace('/tmp/level25_cusp_aux','/tmp/level25_secondcharts_independent_cusp_aux').replace('/tmp/level25_root_chart1','/tmp/level25_secondcharts_independent_root_chart1')
def rd(p,*a,**k):
 actual=Path(transform(str(p)));h=hashlib.sha256(actual.read_bytes()).hexdigest()
 (sources if str(actual).startswith(str(base)) else inputs)[str(actual)]=h
 return read0(actual,*a,**k)
def wr(p,data,*a,**k):
 actual=Path(transform(str(p)))
 if actual==base/'level25_root_chart1_modulus_certificate.json':actual=Path('/tmp/level25_secondcharts_independent_root_chart1_modulus_certificate.json')
 assert str(actual).startswith('/tmp/level25_secondcharts_independent_'),actual
 if actual.suffix=='.m':data=transform(data)
 result=write0(actual,data,*a,**k);outputs[str(actual)]=hashlib.sha256(actual.read_bytes()).hexdigest();return result
Path.read_text=rd;Path.write_text=wr
sys.argv=[str(source)]+args[stage];ns={'__file__':str(source),'__name__':'__main__'}
start=time.monotonic();status='FAIL'
try:
 text=source.read_text()
 if stage=='export':
  assert text.count('exec(src[:cut]);assert not R')==1
  text=text.replace('exec(src[:cut]);assert not R','exec(src);assert not R')
 exec(compile(text,str(source),'exec'),ns);status='PASS'
finally:
 Path.read_text=read0;Path.write_text=write0
 p=Path('/tmp/level25_secondcharts_independent_'+sign+'_'+stage+'_audit.json')
 p.write_text(json.dumps({'stage':stage,'sign':sign,'status':status,'elapsed_seconds':time.monotonic()-start,'sources':sources,'inputs':inputs,'outputs':outputs,'additional_source_free_assertions':stage=='export'},indent=2)+'\n')
 print('INDEPENDENT_STAGE',sign,stage,status,flush=True)
