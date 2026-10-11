from pathlib import Path
import re,hashlib,json,difflib,shutil
base=Path('/data/h4_strict_upgrade_2026-10-10/submission/Wang_Zinan_H4_Independent_Submission')
src=base/'companion/formalized_extensions';dst=base/'companion/reviewed_extension_core'
assert not dst.exists(), 'Derived directory already exists; inspect before regeneration'
(dst/'H4Formal').mkdir(parents=True);(dst/'evidence').mkdir();(dst/'scripts').mkdir()
changes={}
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
def read(n):return (src/'H4Formal'/f'{n}.lean').read_text()
def header(s):return s[:s.index('namespace H4Formal')]
def body(s):return s[s.index('namespace H4Formal'):]
def segment(s,start,end):return s[s.index(start):s.index(end)].rstrip()+'\n'
def generated(name,origin,imports,pieces,note):
 s=read(origin);selected=[segment(s,a,b) for a,b in pieces]
 out=''.join('import '+x+'\n' for x in imports)+'\nnamespace H4Formal\n\nset_option maxRecDepth 32768\nset_option maxHeartbeats 0\n\n'+'\n'.join(selected)+'\nend H4Formal\n'
 changes[name]=(out,origin,note,[{'start':a,'before':b,'original_start_line':s[:s.index(a)].count('\n')+1,'original_end_line':s[:s.index(b)].count('\n'),'segment_sha256':digest(x)} for (a,b),x in zip(pieces,selected)])
# Definitions and arithmetic required by retained extensions only, all copied exactly.
generated('HostSizes','GlobalClaims',['H4Formal.ConcreteCompression'],[
 ('def branchFactor','def originalTypeCopyCount'),
 ('theorem canonicalRepairCellCount_eq_power','theorem hostSideLength_eq_construction')],
 'Extract only branchFactor, hostSideLength, canonicalRepairCellCount and the exact power identity; do not import unrelated native_decide regression theorems.')
generated('TerminalTypes','TerminalClassification',['H4Formal.Host'],[
 ('def terminalMode','theorem block_eq_anchor_of_fields')],
 'Extract only the terminalMode and TerminalForm definitions, not certified classification.')
generated('FiniteMultiplicity','FiniteHost',['H4Formal.Host'],[
 ('def multiplicity','def weightedCompletions')],
 'Extract only the multiplicity definition required by general fiber counting; exclude unrelated native_decide finite regressions.')
# Preserve core declarations byte-for-byte, replace imports only and cut before global integrations.
s=read('PhysicalHost');cut=s.index('theorem repaired_physical_free_all_depth')
out=s[:cut].replace('import H4Formal.TerminalClassification','import H4Formal.HostOrderCompression').replace('import H4Formal.GlobalClaims','import H4Formal.HostSizes')+'end H4Formal\n'
changes['PhysicalHostCore']=(out,'PhysicalHost','Retain all physical host definitions, valid block and quotient correspondence declarations; omit the final two all-depth certificate-dependent conclusions.',[{'original_start_line':1,'original_end_line':s[:cut].count('\n'),'retained_body_sha256':digest(body(s[:cut]))}])
s=read('IndexedMatrix');cut=s.index('theorem indexed_minimum_edit_count')
out=s[:cut].replace('import H4Formal.PhysicalCounting','import H4Formal.EditForcing').replace('import H4Formal.EditDistance','import Mathlib.Algebra.Field.Rat')+'end H4Formal\n'
changes['IndexedMatrixCore']=(out,'IndexedMatrix','Retain numeric matrix definitions, generic indexing/cardinality/edit correspondence; omit theorem-specific exact count and exact repair integration.',[{'original_start_line':1,'original_end_line':s[:cut].count('\n'),'retained_body_sha256':digest(body(s[:cut]))}])
for name,replacements in {
 'PhysicalOrder':[('import H4Formal.PhysicalHost','import H4Formal.PhysicalHostCore')],
 'PhysicalRepresentatives':[('import H4Formal.PhysicalHost','import H4Formal.PhysicalHostCore\nimport H4Formal.TerminalTypes')],
 'GeneralPhysicalCompression':[('import H4Formal.IndexedMatrix','import H4Formal.IndexedMatrixCore')],
 'MarkerPermutation':[('import H4Formal.IndexedMatrix','import H4Formal.IndexedMatrixCore')],
 'GeneralPhysicalCounting':[('import H4Formal.FiniteHost','import H4Formal.FiniteMultiplicity')]
}.items():
 s=read(name);out=s
 for a,b in replacements: assert out.count(a)==1;out=out.replace(a,b)
 assert body(s)==body(out)
 changes[name]=(out,name,'Imports only; every namespace declaration, theorem statement and proof body byte-identical.',[{'declaration_body_sha256':digest(body(s))}])
# Dependency closure of the retained extension roots, with rewritten source contents.
roots=['GeneralPhysicalCompression','MarkerPermutation','GeneralPhysicalCounting'];todo=roots[:];seen=set();alltexts={}
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n in changes:s=changes[n][0]
 else:s=read(n)
 assert not re.search(r'^import H4Formal\.(?:Certificates|CertifiedQueries|CertificateBridge|BV)',s,re.M),n
 assert not re.search(r'\bnative_decide\b|\bsorry\b|\badmit\b|^axiom\b',s,re.M),n
 alltexts[n]=s
 for x in re.findall(r'^import H4Formal\.(\S+)',s,re.M):todo.append(x)
records=[];diff=[]
for n,s in sorted(alltexts.items()):
 f=dst/'H4Formal'/f'{n}.lean';f.write_text(s)
 origin=changes[n][1] if n in changes else n;original=read(origin)
 rec={'derived':'H4Formal/'+n+'.lean','original':'H4Formal/'+origin+'.lean','original_sha256':digest(original),'derived_sha256':digest(s),'change_kind':'exact_copy' if n not in changes else changes[n][2],'preserved_segments':changes[n][3] if n in changes else []}
 records.append(rec)
 if n in changes:diff.extend(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile='formalized_extensions/H4Formal/'+origin+'.lean',tofile='reviewed_extension_core/H4Formal/'+n+'.lean'))
(dst/'H4Formal.lean').write_text('import H4Formal.GeneralPhysicalCompression\nimport H4Formal.MarkerPermutation\nimport H4Formal.GeneralPhysicalCounting\n')
for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']:shutil.copyfile(base/n,dst/n)
(dst/'evidence/source_provenance.json').write_text(json.dumps({'scope':'Derived certificate-free extension core; original companion is unchanged; not the full companion/global H4 route.','original_root':'../formalized_extensions','namespace_policy':'Original H4Formal names preserved in a separately compiled project; no main-project H4Formal olean may be reused.','roots':roots,'retained_project_modules':len(alltexts)+1,'files':records},indent=2)+'\n')
(dst/'evidence/import_refactor.diff').write_text(''.join(diff))
shutil.copyfile('/tmp/derive_h4_extension_core.py',dst/'scripts/derivation_record.py')
print('Created',dst,'modules',len(alltexts)+1)
print('Derived full namespace body hashes:',[(n,digest(body(alltexts[n]))) for n in roots])
