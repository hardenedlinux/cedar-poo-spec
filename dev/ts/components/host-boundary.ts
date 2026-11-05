// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import {composeHeading,type FigureContext} from '@deterministic-engineering/render';
import {repositoryPath} from '../sources';
const ids=['exact-handoff','changed-bytes','missing-fact','stale-writer','missing-durable-ack','pause-before-handoff','lost-reply-retry'] as const;
const path='dev/.generated/binance2026-metadata.json';
const Schema=v.object({host:v.array(v.object({id:v.picklist(ids),admitted:v.boolean()}))});
export async function captureHostBoundary(root:string){
 const raw=await readFile(await repositoryPath(root,path),'utf8'),observations=v.parse(Schema,JSON.parse(raw)).host;
 if(observations.map(value=>value.id).join()!==ids.join())throw new Error('Host observations must retain every ordered boundary case');
 return{observations,sources:{[path]:raw}};
}
export type HostBoundary=Awaited<ReturnType<typeof captureHostBoundary>>;
/** A teaching flow with actual fixture outcomes; physical guarantees stay amber. */
export function composeHostBoundary(context:FigureContext,boundary:HostBoundary){
 const headings:ReturnType<typeof composeHeading>[]=[];
 const h=(text:string,role='note')=>{const part=composeHeading(context,{text,role});headings.push(part);return part.markup;};
 const arrow='<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" width="36" height="24" viewBox="0 0 36 24"><path d="M2 12h29m-8-8 8 8-8 8" fill="none" stroke="#167d78" stroke-width="3"/></svg>';
 const icon=(id:string,glyph:string,admitted:boolean)=>`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-host-observation="${id}" data-admitted="${admitted}" width="80" height="80" viewBox="0 0 64 64">${context.glyph(glyph).replace('<svg ','<svg width="64" height="64" ')}</svg>`;
 const positive=boundary.observations[0]!;
 const stages=[['registrar','1 · Authenticate','Exact workload + command'],['rules','2 · Bind bytes','Pinned decoder + payment'],['evidence','3 · Commit first','Exact before / after journal'],['gate','4 · Recheck and hand off','Consume slot; retain unknown']];
 const flow=stages.map(([glyph,title,detail],index)=>`${index?`<div class="host-arrow">${arrow}</div>`:''}<article class="host-stage" data-surface="rectangle">${icon(positive.id,glyph!,positive.admitted)}${h(title!,'heading')}${h(detail!)}${h(positive.admitted?'FIXTURE PATH PASSED':'FIXTURE PATH REFUSED','classification')}</article>`).join('');
 const names:Record<typeof ids[number],readonly[string,string]>={
  'exact-handoff':['gate','Exact handoff'],'changed-bytes':['fingerprint','Swapped signing bytes'],
  'missing-fact':['evidence','Missing current evidence'],'stale-writer':['current','Old writer / journal'],
  'missing-durable-ack':['pending','Invented commit receipt'],'pause-before-handoff':['warning','Paused before handoff'],
  'lost-reply-retry':['recovery','Retry after lost response']};
 const attacks=boundary.observations.slice(1).map(value=>{const[glyph,title]=names[value.id];return `<article class="host-refusal" data-surface="rectangle">${icon(value.id,glyph,value.admitted)}<div>${h(title,'heading')}${h(value.admitted?'ADMITTED':'REFUSED','classification')}</div></article>`;}).join('');
 return{markup:`<section class="host-audit">${h('A payment must cross four checked doors','heading')}<div class="host-stages">${flow}</div><aside class="physical-boundary" data-surface="rectangle">${h('AMBER BOUNDARY · REAL SIGNER + STORAGE + CHAIN','classification')}${h('The Host must realize the decoder, trust roots, atomic handoff and antirollback storage.')}${h('A lying verifier or replayed old snapshot can defeat the modeled boundary.')}</aside>${h('Six ways to stop the same payment before it becomes an effect','heading')}<div class="host-refusals">${attacks}</div>${h('Observed synthetic Lean results. No live key, blockchain codec, storage crash test or HSM enforcement is claimed.')}</section>`,css:headings.map(value=>value.css).join('\n')+`.host-audit{margin:24px 0}.host-stages{display:grid;grid-template-columns:1fr 36px 1fr 36px 1fr 36px 1fr;gap:12px;align-items:center;margin:20px 0}.host-stage{border:2px solid #167d78;border-radius:12px;padding:16px;background:#f2faf6;min-height:220px}.host-arrow{display:flex;justify-content:center}.physical-boundary{padding:18px;border:2px dashed #b07b27;border-radius:12px;background:#fff8e9;margin:22px 0}.host-refusals{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:16px;margin:18px 0}.host-refusal{display:flex;gap:12px;align-items:center;padding:14px;border:2px solid #ba514b;border-radius:12px;background:#fff6f3}.host-refusal>svg{flex:none}`};
}
