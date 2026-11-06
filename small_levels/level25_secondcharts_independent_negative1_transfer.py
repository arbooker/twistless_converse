"""Bind the final transfer certificate to fresh negative and audited positive rows."""
from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def canon(s):return re.sub(r'\s+','',s.replace('\\',''))
source=base/'level25_plus_poles_negative1_generic_audit_transfer.m';text=source.read_text()
fresh=Path('/tmp/level25_secondcharts_independent_plus_poles_negative1_generic_audit_relations.txt')
negative=re.search(r'P:=(\[.*?\])\s*;I:=',text,re.S).group(1)
assert canon(negative)==canon(fresh.read_text())
assert len(negative[1:-1].split(','))==14
positive=re.search(r'Positive:=\[T\|(.*?)\];',text,re.S).group(1).split(',')
data=base/'level25_plus_poles_chart1_rows.json';rows=json.loads(data.read_text());assert len(rows)==len(positive)==15
mapped=[re.sub(r'\b[A-YX]+\b',lambda m:{'A':'a','Y':'y','X':'x'}.get(m[0],m[0]),p) for p in rows]
assert all(canon(a)==canon(b) for a,b in zip(mapped,positive))
assert 'assert NormalForm(SS^2,J) eq 0;' in text
assert 'assert NormalForm(num,I) eq 0;' in text
assert 'for unit in [Numerator(xx),Numerator(d0),Numerator(u0)]' in text
assert 'assert TotalDegree(den) eq 0;' in text
assert text.count('GlobalModular:=false')==2 and 'SetGBGlobalModular(false)' in text
out=Path('/tmp/level25_secondcharts_independent_negative1_transfer.m');out.write_text(text)
record={'status':'PASS_LITERAL_INPUT_PROVENANCE','transfer_source_sha256':sha(source),'fresh14_sha256':sha(fresh),'positive15_sha256':sha(data),'negative14_literal_equality':True,'positive15_literal_equality':True,'transfer_copy_sha256':sha(out),'builder_sha256':sha(__file__)}
Path('/tmp/level25_secondcharts_independent_negative1_transfer_input_audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS_LITERAL_14_AND_15_ROWS',out)
