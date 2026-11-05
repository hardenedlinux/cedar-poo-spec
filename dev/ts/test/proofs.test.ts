// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect,afterAll} from 'bun:test';
import {readFile,readdir} from 'node:fs/promises';
import {connectWasm} from '@openmbee/opensysml';
import {verifyFigure,receiptArtifact} from '../artifacts';
import {readProofMap,leanProofCheck,type ProofMap} from '../proofs';
const root=new URL('../../../',import.meta.url),source='dev/sysml/zero-trust-proofs.sysml';
// One SDK-owned worker per suite; each source variant still parses and is checked.
// Do not cache ProofMaps or rejection results across source mutations.
let connection:ReturnType<typeof connectWasm>|undefined;
afterAll(async()=>{if(connection)await(await connection).close();});
async function observe(raw:string){
 const started=performance.now(),host=await(connection??=connectWasm()),connected=performance.now();
 const model=(await host.parseSources([['Project.sysml',await readFile(new URL('Project.sysml',root),'utf8')],[source,raw]])).raiseForErrors(),parsed=performance.now();
 try{return await readProofMap(model,'ZeroTrustProofs');}
 finally{await model.close();console.log('SDK-PROOF-STAGES',JSON.stringify({sourceSHA256:Bun.SHA256.hash(raw,'hex'),connect_ms:connected-started,parse_ms:parsed-connected,observe_ms:performance.now()-parsed}));}
}
function check(map:ProofMap){
 const checked=Bun.spawnSync(['lake','env','lean','-M','2048','-T','10000000','--stdin'],{cwd:root.pathname,stdin:Buffer.from(leanProofCheck(map))});
 return{code:checked.exitCode,signal:checked.signalCode,stdout:new TextDecoder().decode(checked.stdout),stderr:new TextDecoder().decode(checked.stderr)};
}
const raw=()=>readFile(new URL(source,root),'utf8');
test('SDK declarations, roles and proof-use references bind emitted receipts',async()=>{
 const started=performance.now(),map=await observe(await raw());expect(map.cards.length).toBeGreaterThan(0);
 for(const card of map.cards)expect((await readFile(new URL(card.source,root),'utf8')).length).toBeGreaterThan(0);
 for(const file of (await readdir(new URL('../../d2/',import.meta.url))).filter(file=>file.endsWith('.d2'))){
  const receipt:{sdk:{view:string};proofClaims?:ProofMap}=JSON.parse(await readFile(new URL(receiptArtifact('dev/d2/'+file),root),'utf8'));
  if(receipt.sdk.view.startsWith('ZeroTrustProofs::'))expect(receipt.proofClaims).toEqual(map);
 }
 console.log('SDK-PROOF-OBSERVATION-MS',Math.round(performance.now()-started));
},30000);
test('native Lean validates the verified SDK proof capture within its own budget',async()=>{
 const entry='dev/d2/zero-trust-model-proofs.d2';await verifyFigure(root.pathname,entry);
 const receipt:{proofClaims:ProofMap}=JSON.parse(await readFile(new URL(receiptArtifact(entry),root),'utf8'));
 const started=performance.now(),result=check(receipt.proofClaims);
 console.log('NATIVE-PROOF-CHECK',JSON.stringify({milliseconds:Math.round(performance.now()-started),code:result.code,signal:result.signal}));
 expect(result).toMatchObject({code:0,stderr:''});expect(result.stdout).toContain('PROOF-FIGURES-LEAN-OK');
},30000);
test('SDK observation tolerates formatting and discovers added declarations without fixed counts',async()=>{
 const original=await raw(),baseline=await observe(original);
 const reformatted=await observe(original.replace('part required : Definition;','// SDK owns syntax\n part\n required :\n Definition;'));
 expect(reformatted.cards).toEqual(baseline.cards);expect(reformatted.uses).toEqual(baseline.uses);
 const extra='part additional : Definition; attribute additionalSymbol : String = "CedarPooSpec.ZeroTrust.Framework"; attribute additionalSource : String = "CedarPooSpec/ZeroTrust/Model.lean";';
 const expanded=await observe(original.replace('view model {',extra+'\nview model {'));
 expect(expanded.cards.length).toBe(baseline.cards.length+1);expect(expanded.cards.some(card=>card.id==='ZeroTrustProofs::additional')).toBe(true);
},30000);
test('SDK proof contracts reject missing metadata, invalid roles and unresolved/unpictured uses',async()=>{
 const original=await raw();
 await expect(observe(original.replace('requiredSymbol','missingSymbol'))).rejects.toThrow();
 await expect(observe(original.replace('part required : Definition;','part def UnknownRole; part required : UnknownRole;'))).rejects.toThrow();
 await expect(observe(original.replace('("ZeroTrustProofs::usage")','("ZeroTrustProofs::notDeclared")'))).rejects.toThrow();
 await expect(observe(original.replace('("ZeroTrustProofs::usage")','("ZeroTrustProofs::observed")'))).rejects.toThrow('no SDK view edge');
 await expect(observe(original.replace('recoveryUses','orphanUses'))).rejects.toThrow('Unbound proof-use owner');
 await expect(observe('package ZeroTrustProofs {}')).rejects.toThrow('Empty');
},30000);
const negativeChecks:[string,(source:string)=>string,string][]=[
 ['missing declaration',source=>source.replace('CedarPooSpec.ZeroTrust.Framework.required','CedarPooSpec.ZeroTrust.Framework.notDeclared'),'missing diagram declaration'],
 ['false theorem role',source=>source.replace('part required : Definition;','part required : KernelLaw;'),'not a theorem'],
 ['source module drift',source=>source.replace('attribute requiredSource : String = "CedarPooSpec/ZeroTrust/Composition.lean"','attribute requiredSource : String = "CedarPooSpec/ZeroTrust/Model.lean"'),'declaration/source mismatch'],
 ['fabricated lemma use',source=>source.replace('("ZeroTrustProofs::usage")','("ZeroTrustProofs::refinement")').replace('view model {','connection fabricated connect refinement to recovery;\n view model { expose fabricated;'),'lemma edge absent from proof term'],
];
for(const[name,change,message]of negativeChecks)test('native Lean refuses '+name,async()=>{
 const result=check(await observe(change(await raw())));
 expect(result.code).not.toBe(0);expect(result.stdout+result.stderr).toContain(message);expect(result.stdout).not.toContain('PROOF-FIGURES-LEAN-OK');
},30000);

test('activity diagrams bind actual Lean API and Final field declarations without claiming trace extraction',async()=>{
 for(const name of ['gateway-profile-workflow','gateway-final-tasks']){
  const entry='dev/d2/'+name+'.d2';await verifyFigure(root.pathname,entry);
  const receipt:{proofClaims:ProofMap}=JSON.parse(await readFile(new URL(receiptArtifact(entry),root),'utf8'));
  expect(receipt.proofClaims.cards.length).toBeGreaterThan(0);
  if(name==='gateway-final-tasks'){
   expect(receipt.proofClaims.record?.fields).toHaveLength(8);
   const missing=check({...receipt.proofClaims,record:{symbol:receipt.proofClaims.record!.symbol,fields:receipt.proofClaims.record!.fields.slice(1)}});
   expect(missing.code).not.toBe(0);expect(missing.stdout+missing.stderr).toContain('task fields are incomplete');
   const substituted=check({...receipt.proofClaims,record:{symbol:receipt.proofClaims.record!.symbol,fields:receipt.proofClaims.record!.fields.map((field,index)=>index===0?'CedarPooSpec.Gateway.PublicationReview.Final.approved':field)}});
   expect(substituted.code).not.toBe(0);expect(substituted.stdout+substituted.stderr).toContain('task fields are incomplete');
  }
  const result=check(receipt.proofClaims);
  expect(result).toMatchObject({code:0,stderr:''});expect(result.stdout).toContain('PROOF-FIGURES-LEAN-OK');
 }
},30000);
