// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {readFile} from 'node:fs/promises';
import {connectWasm} from '@openmbee/opensysml';
import {readProofMap,leanProofCheck,type ProofMap} from '../proofs';
const root=new URL('../../',import.meta.url),source='dev/sysml/zero-trust-proofs.sysml';
async function observe(raw:string){
 const connection=await connectWasm();
 try{return await readProofMap((await connection.parseSources([[source,raw]])).raiseForErrors(),'ZeroTrustProofs');}
 finally{await connection.close();}
}
function check(map:ProofMap){
 const checked=Bun.spawnSync(['lake','env','lean','-M','2048','-T','10000000','--stdin'],{cwd:root.pathname,stdin:Buffer.from(leanProofCheck(map))});
 return{code:checked.exitCode,stdout:new TextDecoder().decode(checked.stdout),stderr:new TextDecoder().decode(checked.stderr)};
}
const raw=()=>readFile(new URL(source,root),'utf8');
test('SDK declarations, roles and proof-use references drive native Lean validation',async()=>{
 const map=await observe(await raw());expect(map.cards.length).toBeGreaterThan(0);
 for(const card of map.cards)expect((await readFile(new URL(card.source,root),'utf8')).length).toBeGreaterThan(0);
 const result=check(map);expect(result).toMatchObject({code:0,stderr:''});expect(result.stdout).toContain('PROOF-FIGURES-LEAN-OK');
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
