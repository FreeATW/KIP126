import csv,json,hashlib,sys
from pathlib import Path
# Usage: python3 E2pageData.generate.py /path/to/extracted/csv [output-directory]
# Inputs are the three original UTF-16 S0_AdamsE2_*.csv files.
if len(sys.argv) not in (2,3):
 raise SystemExit('usage: E2pageData.generate.py CSV_DIRECTORY [OUTPUT_DIRECTORY]')
src=Path(sys.argv[1])
dst=Path(sys.argv[2]) if len(sys.argv)==3 else Path(__file__).resolve().parent
expected_sha256 = {
 'generators': '3c4e45a1e28837e651e729bee14e7c62a99f797bc650d69e8a79aec13a762c72',
 'relations': '8b4b67d6fb3c9a3a264813ea780340e73b1a66290c8616d3308ae1fc19f3add5',
 'basis': '6a337964ad3ac02b729a46fd839dced7cb6764d14d4cea413163987eba8de871',
}
for kind, expected in expected_sha256.items():
 actual = hashlib.sha256((src/f'S0_AdamsE2_{kind}.csv').read_bytes()).hexdigest()
 if actual != expected:
  raise SystemExit(f'{kind}: SHA-256 mismatch; expected pinned v126.3.cw49 input')
def read(k): return list(csv.DictReader((src/f'S0_AdamsE2_{k}.csv').open(encoding='utf-16')))
gens,rels,basis=map(read,['generators','relations','basis'])
assert [int(r['id']) for r in gens]==list(range(len(gens)))
deg=[(int(r['s']),int(r['stem'])+int(r['s'])) for r in gens]
def mon(s):
 if s=='': return []
 ns=list(map(int,s.split(','))); assert len(ns)%2==0
 ps=list(zip(ns[::2],ns[1::2])); assert all(0<=i<len(gens) and a>0 for i,a in ps)
 assert [i for i,a in ps]==sorted(set(i for i,a in ps))
 return ps
def degree(s):
 ps=mon(s); return tuple(sum(deg[i][j]*a for i,a in ps) for j in (0,1))
for r in rels:
 d=(int(r['s']),int(r['stem'])+int(r['s'])); assert d[1]<=261
 assert all(degree(m)==d for m in r['rel'].split(';'))
seen=set()
for r in basis:
 d=(int(r['s']),int(r['stem'])+int(r['s'])); assert degree(r['mon'])==d
 key=(*d,int(r['index'])); assert key not in seen; seen.add(key)
assert [r['rel'] for r in rels[:3]]==['0,1,1,1','1,1,2,1','1,3;0,2,2,1']
q=lambda s:json.dumps(s,ensure_ascii=False)
header='''/-!
Generated from https://zenodo.org/records/14875701 (v126.3.cw49),
kervaire_csv.rar. The three source files are UTF-16 CSV.
All rows are retained; degrees are converted from (stem,s) to (s,t).
The d2 column is deliberately not imported: this module supplies E2 algebra data.
SHA-256 of the original CSV bytes:
'''
for k in ['generators','relations','basis']:
 p=src/f'S0_AdamsE2_{k}.csv'; header+=f'{p.name}: {hashlib.sha256(p.read_bytes()).hexdigest()}\n'
header+='-/'
parts=[header,'set_option maxRecDepth 16384','namespace KIPBase.SphereE2.Data',f'def generatorCount : Nat := {len(gens)}',f'def relationCount : Nat := {len(rels)}',f'def basisCount : Nat := {len(basis)}',
'''/-- (name, cohomological degree s, internal degree t), indexed by CSV id. -/
def generators : Array (String × Nat × Nat) := #[
'''+',\n'.join(f'  ({q(r["name"])}, {s}, {t})' for r,(s,t) in zip(gens,deg))+ '\n]',
'''/-- First three CSV relations, kept separate for small kernel-checked examples. -/
def firstRelations : List String := ["0,1,1,1", "1,1,2,1", "1,3;0,2,2,1"]''']
# Chunks keep individual string literals modest. Newlines separate rows, never terms.
strings=[r['rel'] for r in rels[3:]]
chunks=['\n'.join(strings[i:i+1024]) for i in range(0,len(strings),1024)]
parts+=['/-- Remaining relation strings, in original row order. -/\ndef relationChunks : Array String := #[\n'+',\n'.join(q(c) for c in chunks)+'\n]',
'''def relations : List String :=
  firstRelations ++ relationChunks.toList.flatMap (fun s => s.splitOn "\\n")''']
bs=[f'{r["s"]}|{int(r["stem"])+int(r["s"])}|{r["index"]}|{r["mon"]}' for r in basis]
chunks=['\n'.join(bs[i:i+1024]) for i in range(0,len(bs),1024)]
parts+=['/-- Basis rows encoded as s|t|local index|monomial; empty monomial is 1. -/\ndef basisChunks : Array String := #[\n'+',\n'.join(q(c) for c in chunks)+'\n]','end KIPBase.SphereE2.Data']
(dst/'E2pageData.lean').write_text('\n\n'.join(parts)+'\n')
print('Validated all generator IDs, monomial encodings, homogeneous relation degrees, basis degrees and unique basis IDs.')
print('Generated',dst/'E2pageData.lean', (dst/'E2pageData.lean').stat().st_size,'bytes')
