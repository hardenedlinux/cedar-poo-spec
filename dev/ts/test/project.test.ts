// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {test,expect,afterAll} from 'bun:test';
import {readFile} from 'node:fs/promises';
import {connectWasm} from '@openmbee/opensysml';
import {projectEntry,readProjectLayout,selectProjectModels} from '../project';
import {captureFiles,assertCurrent,sha} from '../sources';
import {readProofMap,leanProofCheck} from '../proofs';
import {verifyFigure} from '../artifacts';
const root=new URL('../../../',import.meta.url);
let connection:ReturnType<typeof connectWasm>|undefined;
afterAll(async()=>{if(connection)await(await connection).close();});
const entry=()=>readFile(new URL(projectEntry,root),'utf8');
async function layout(source:string){
 const host=await(connection??=connectWasm()),model=(await host.parseSources([[projectEntry,source]])).raiseForErrors();
 try{return await readProjectLayout(model);}finally{await model.close();}
}
test('Project.sysml owns the typed development layout and declared SysML inputs',async()=>{
 const declared=await layout(await entry());
 expect(declared).toMatchObject({typescriptRoot:'dev/ts',sysmlRoot:'dev/sysml',quintRoot:'dev/qnt'});
 const sources=await captureFiles(root.pathname,[projectEntry,...declared.modelSources]);
 const host=await(connection??=connectWasm()),model=(await host.parseSources(Object.entries(sources))).raiseForErrors();
 try{expect(await readProjectLayout(model)).toEqual(declared);}finally{await model.close();}
 expect(selectProjectModels(declared,['dev/sysml/architecture.sysml'])).toEqual(['Project.sysml','dev/sysml/architecture.sysml']);
 expect(()=>selectProjectModels(declared,['dev/sysml/unregistered.sysml'])).toThrow('not declared');
},30000);
test('real SDK project attributes reject duplicate, escaping and wrong-owner source declarations',async()=>{
 const original=await entry();
 await expect(layout(original.replace('"Examples/Scenarios/TenantDevicePolicyEvolution.d2"','"Examples/Scenarios/../outside.d2"'))).rejects.toThrow('escapes');
 await expect(layout(original.replace('"dev/ts"','"dev/other"'))).rejects.toThrow('roots');
 await expect(layout(original.replace('"dev/sysml/architecture.sysml"','"dev/sysml/../outside.sysml"'))).rejects.toThrow('escapes');
 await expect(layout(original.replace('"dev/sysml/architecture.sysml"','"dev/sysml/architecture.sysml", "dev/sysml/architecture.sysml"'))).rejects.toThrow('unique feature');
},30000);
test('Project.sysml source bytes participate in the existing publication invalidation boundary',async()=>{
 const original=await entry();await assertCurrent(root.pathname,{[projectEntry]:sha(original)});
 await expect(assertCurrent(root.pathname,{[projectEntry]:sha(original+'\n')})).rejects.toThrow('changed');
});
test('the incident assurance model names real shared and financial Lean declarations',async()=>{
 const source='dev/sysml/attackers.sysml',host=await(connection??=connectWasm());
 const model=(await host.parseSources(Object.entries(await captureFiles(root.pathname,[projectEntry,source])))).raiseForErrors();
 try{
  const claims=await readProofMap(model,'FinancialAttackers');
  expect(claims.cards.some(card=>card.symbol==='CedarPooSpec.Attackers.ProfileObject.selection_retains_actual_parent')).toBe(true);
  expect(claims.cards.some(card=>card.role==='HostPremise')).toBe(true);
  for(const namespace of ['FinancialAttackers','WalletSigningProofs','TenantScenarioProofs','PaymentDefenseFlow']){
  const selected=await readProofMap(model,namespace);
  const checked=Bun.spawnSync(['lake','env','lean','-M','2048','-T','10000000','--stdin'],{cwd:root.pathname,stdin:Buffer.from(leanProofCheck(selected))});
  expect(checked.exitCode).toBe(0);expect(new TextDecoder().decode(checked.stdout)).toContain('PROOF-FIGURES-LEAN-OK');
  }
 }finally{await model.close();}
},30000);

test('every project-declared scenario publishes adjacent source-bound SVG exports',async()=>{
 const declared=await layout(await entry());
 expect(declared.scenarioFigures).toEqual([
  'Examples/Scenarios/FinancialServices/Wallet/Base.d2',
  'Examples/Scenarios/FinancialServices/Wallet/Binance2026.d2',
  'Examples/Scenarios/FinancialServices/Wallet/Binance2026Assurance.d2',
  'Examples/Scenarios/TenantDevicePolicyEvolution.d2'
 ]);
 for(const figure of declared.scenarioFigures){
  await verifyFigure(root.pathname,figure);
  const receipt=JSON.parse(await readFile(new URL(figure.slice(0,-3)+'.json',root),'utf8'));
  expect(receipt.entry).toBe(figure);
  expect(receipt.sources[projectEntry]).toBe(sha(await entry()));
  expect(receipt.receipt.readability.minimumTextSize).toBeGreaterThanOrEqual(12);
  expect(receipt.proofClaims.modelHash).toBe(receipt.sdk.modelHash);
  expect(await Bun.file(new URL(figure.slice(0,-3)+'.svg',root)).exists()).toBe(true);
 }
},30000);
