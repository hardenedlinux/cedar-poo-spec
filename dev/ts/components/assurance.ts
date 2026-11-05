// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import type {FigureContext,FigureComposer} from '@deterministic-engineering/render';
import type {ProofMap} from '../proofs';
type Composition=ReturnType<FigureComposer>;
const teal='#167d78',red='#ba514b',gold='#b07b27',ink='#263845';
/** Local explanatory miniatures. They illustrate one captured declaration, not extra proof edges. */
export function componentIllustrations(context:FigureContext,proofs:ProofMap):ReadonlyMap<string,Composition>{
 const text=(x:number,y:number,label:string,color=ink)=>`<text x="${x}" y="${y}" fill="${color}" font-size="14" font-family="Inter,sans-serif" text-anchor="middle">${context.text(label)}</text>`;
 const box=(x:number,y:number,w:number,h:number,label:string,color=teal)=>`<rect x="${x}" y="${y}" width="${w}" height="${h}" rx="8" fill="white" stroke="${color}" stroke-width="2"/>${text(x+w/2,y+h/2+5,label,color)}`;
 const arrow=(x:number,y:number,to:number,color=teal)=>`<path d="M${x} ${y}H${to-7}m-6-5 6 5-6 5" fill="none" stroke="${color}" stroke-width="2"/>`;
 const line=(x:number,y:number,x2:number,y2:number,color=teal)=>`<path d="M${x} ${y}L${x2} ${y2}" fill="none" stroke="${color}" stroke-width="2"/>`;
 const draw=(symbol:string):[string,string]=>{
  if(symbol.endsWith('ProfileObject.Model'))return ['capability-graph',box(4,10,94,34,'Known access',red)+arrow(100,27,132,red)+box(134,10,92,34,'Rule',red)+arrow(228,27,260,red)+box(262,10,94,34,'Reachable',red)+box(94,75,172,32,'Signing right is separate')];
  if(symbol.endsWith('selection_retains_actual_parent'))return ['parent-selection',box(121,3,118,29,'Shared root')+line(180,32,80,58)+line(180,32,280,58)+box(9,58,140,30,'Endpoint + AI')+box(211,58,140,30,'Deployment')+line(80,88,180,110)+line(280,88,180,110)+text(180,128,'Select both actual parents')];
  if(symbol.endsWith('certified_isolation'))return ['isolation-boundary',box(5,35,110,40,'Attacker rules',red)+arrow(117,55,172,red)+`<path d="M183 10V105" stroke="${teal}" stroke-width="7"/>`+box(209,35,146,40,'Protected outputs')+text(180,128,'No modeled rule crosses this boundary')];
  if(symbol.endsWith('run_preserves_outputs'))return ['trace-invariant',box(2,25,89,38,'State 0')+arrow(93,44,133)+box(135,25,89,38,'State 1')+arrow(226,44,267)+box(269,25,89,38,'State n')+text(180,101,'Every admitted step retains isolation')];
  if(symbol.endsWith('release_binds_exact_transaction'))return ['exact-transaction',box(4,8,142,78,'Approved payment')+text(75,66,'to · amount · nonce')+text(180,55,'=')+box(214,8,142,78,'Released transfer')+text(285,66,'to · amount · nonce')+text(180,121,'Changing the transaction breaks admission')];
  if(symbol.endsWith('deployment_cannot_release'))return ['purpose-separation',box(3,20,132,45,'Deployment key',red)+arrow(137,42,181,red)+`<path d="M190 7V92" stroke="${red}" stroke-width="5"/>`+box(221,20,136,45,'Signing purpose')+text(180,122,'Network access does not grant payment authority')];
  if(symbol.endsWith('release_only_native_transfer'))return ['transfer-shape',box(3,10,155,35,'Native transfer')+box(202,10,155,35,'Accepted shape')+arrow(160,27,200)+box(36,77,288,34,'No calldata · no code delegation',red)];
  if(symbol.endsWith('delegated_cannot_release'))return ['delegation-quarantine',box(3,20,143,42,'Delegation live',gold)+arrow(148,41,200,gold)+box(202,20,155,42,'Signing blocked',red)+text(180,122,'A clean record from another wallet cannot help')];
  if(symbol.endsWith('no_signing_after_pause'))return ['sticky-pause',box(3,20,112,42,'Pause',gold)+arrow(117,41,150)+box(152,20,205,42,'Recover / observe / clear')+text(180,122,'Every finite control trace still refuses signing')];
  if(symbol.endsWith('recovery_retains_burns'))return ['retained-consumption',box(3,20,146,42,'Consumed nonce')+arrow(151,41,205)+box(207,20,149,42,'Still consumed')+text(180,122,'An old live ledger cannot replace the journal')];
  if(symbol.endsWith('observation_cannot_resume'))return ['clear-without-resume',box(3,20,147,42,'Code cleared')+arrow(152,41,207,gold)+box(209,20,148,42,'Still paused',gold)+text(180,122,'Verified removal is not payment permission')];
  if(symbol.endsWith('release_retains_gateway'))return ['current-gateway',box(5,30,101,38,'Current state')+arrow(108,49,133)+box(135,17,91,64,'Effect gate')+arrow(228,49,253)+box(255,30,100,38,'Signing')+text(180,121,'Recheck at the moment of use')];
  if(symbol.endsWith('revoked_cannot_release'))return ['revoked-path',box(7,28,105,40,'Revoked',red)+arrow(114,48,165,red)+`<path d="M174 17V82M162 36l24 24m0-24-24 24" stroke="${red}" stroke-width="4"/>`+box(220,28,134,40,'No new signature',red)+text(180,121,'A later request cannot reuse revoked authority')];
  if(symbol.endsWith('pause_preserves_outstanding_authority'))return ['delegation-residue',box(5,5,150,34,'Withdrawals paused',gold)+text(180,29,'≠',gold)+box(207,5,148,34,'Chain authority gone',gold)+box(52,72,256,35,'Delegation remains until verified clear',gold)];
  if(symbol.endsWith('PaymentSigning.Current'))return ['host-boundary',box(2,27,138,43,'Real identity / chain',gold)+arrow(142,49,206,gold)+`<path d="M182 3V100" stroke="${gold}" stroke-width="2" stroke-dasharray="5 5"/>`+box(208,27,150,43,'Modeled current facts')+text(180,123,'The Host must make these facts authentic',gold)];
  if(symbol==='CedarPooSpec.Scenarios.Metadata')return ['scenario-provenance',box(3,10,105,42,'Publisher')+box(128,10,105,42,'Event date')+box(253,10,105,42,'Disclosure')+line(55,52,180,84)+line(180,52,180,84)+line(305,52,180,84)+box(80,84,200,34,'Mandatory typed provenance')];
  if(symbol.endsWith('derivation_retains_parent'))return ['scenario-lineage',box(3,20,131,50,'Wallet parent')+arrow(136,45,190)+box(192,20,164,50,'Incident scenario')+text(180,119,'The child retains exact parent metadata')];
  if(symbol==='CedarPooSpec.Binance2026Scenario.metadata')return ['incident-source',box(3,20,147,44,'29 Oct: wallet abuse',red)+arrow(152,42,208,gold)+box(210,20,147,44,'3 Nov: report',gold)+text(180,119,'Preliminary; AI exploit mechanism unknown',gold)];
  if(symbol==='CedarPooSpec.WalletSigningExample.scenario')return ['wallet-inputs',box(3,13,145,44,'Current wallet')+text(180,43,'+')+box(212,13,145,44,'Exact request')+line(75,57,180,94)+line(285,57,180,94)+text(180,120,'One typed synthetic acceptance scenario')];
  if(symbol==='CedarPooSpec.TenantDeviceAuthorizationExample.scenario')return ['tenant-device',box(3,20,129,42,'Same tenant')+text(180,47,'AND')+box(228,20,129,42,'Trusted device')+text(180,119,'Both policy conditions must be satisfied')];
  throw new Error('Missing explanatory component illustration: '+symbol);
 };
 return new Map(proofs.cards.map(card=>{const[kind,body]=draw(card.symbol);return[card.id,{markup:`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-component-illustration="${kind}" data-lean-symbol="${context.text(card.symbol)}" width="360" height="140" viewBox="0 0 360 140" role="img" aria-label="Conceptual explanation of ${context.text(card.symbol)}">${body}</svg>`,css:'.component-miniature{margin:12px 0 8px}.component-miniature>svg{display:block;max-width:100%;height:auto}'}];}));
}
