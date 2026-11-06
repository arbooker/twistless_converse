"""Compare freshly regenerated chart polynomials to stable worker certificates.
Export fresh assertion-based Magma checks; no worker outputs are trusted.
"""
from pathlib import Path
import sys,re,json,hashlib
eta=int(sys.argv[1]);tag='plus' if eta==1 else 'minus'
base=Path(__file__).parent
reference=base/('level25_cusp_aux_zero2_'+tag+'_certificate.m')
ref=reference.read_text();blocks=re.findall(r'P:=\[R\|(.*?)\];',ref,re.S);assert len(blocks)==2
manifest={'eta':eta,'reference':str(reference),'reference_sha256':hashlib.sha256(reference.read_bytes()).hexdigest(),'charts':[]}
for chart,block in enumerate(blocks):
 source=Path('/tmp/level25_zero2_independent_prime7_firstjet_ideal_'+str(eta)+'_zero2_'+str(chart)+'.m')
 text=source.read_text();fresh=re.findall(r'P:=\[R\|(.*?)\];',text,re.S);assert len(fresh)==1
 assert re.sub(r'\s+','',block)==re.sub(r'\s+','',fresh[0]),('polynomial-list mismatch',eta,chart)
 checked=Path('/tmp/level25_zero2_independent_checked_'+str(eta)+'_'+str(chart)+'.m')
 checked.write_text(text[:text.index('print "BEGIN"')]+'assert 1 in ideal<R|P>; print "INDEPENDENT_ZERO2_'+str(eta)+'_CHART_'+str(chart)+'_PASS"; quit;\n')
 manifest['charts'].append({'chart':chart,'original_export_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'checked_path':str(checked),'checked_sha256':hashlib.sha256(checked.read_bytes()).hexdigest(),'polynomial_list_match':True})
print('PASS: both freshly regenerated polynomial lists exactly match stable certificate',eta)
Path('/tmp/level25_zero2_independent_compare_'+str(eta)+'.json').write_text(json.dumps(manifest,indent=2))
