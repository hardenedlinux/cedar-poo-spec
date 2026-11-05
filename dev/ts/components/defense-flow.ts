// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {composeDiagram,modelDiagram,type FigureContext} from '@deterministic-engineering/render';
import {captureArtwork,type Artwork} from './artwork';
import type {IncidentStory} from './incident';
import type {FinancialArtwork} from './financial';
const ids=['purpose','approval','exact','freshness','transfer'] as const;
export type DefenseArtwork=Artwork<typeof ids[number]>;
export const captureDefenseArtwork=(root:string)=>captureArtwork(root,'dev/assets/financial/defense/artwork.json',ids,'dev/assets/financial/defense');
/** The SDK owns every node/edge. Actual Lean fixture outcomes select the visible path state. */
export function composeDefenseFlow(context:FigureContext,artwork:DefenseArtwork,financial:FinancialArtwork,story:IncidentStory){
 if(!context.model||!story.defense.deployment_refused||!story.defense.valid_transfer_released)throw new Error('Defense flow requires the observed negative and positive Lean controls');
 const model={...context.model,relations:context.model.relations.map(edge=>({...edge,srcArrow:'none' as const,dstArrow:'arrow' as const}))};
 const key=(name:string)=>name.slice(name.lastIndexOf('::')+2);
 const byId=new Map(model.subjects.map(node=>[node.id,key(node.sourceName!)]));
 const status=(id:string)=>id==='purpose'?'FAILED':id==='joint'?'REFUSED':id==='refused'?'NO SIGNATURE':id==='released'?'NOT REACHED':id==='host'?'HOST PREMISE':'REQUIRED';
 const roles=Object.fromEntries(model.subjects.map(node=>[node.id,['purpose','joint','refused'].includes(key(node.sourceName!))?'counter':key(node.sourceName!)==='released'?'pending':'default']));
 const specification=modelDiagram(model,{roles,edgeLabels:false,options:{'elk.direction':'DOWN','elk.algorithm':'layered','elk.edgeRouting':'ORTHOGONAL','elk.spacing.nodeNode':'20','elk.layered.spacing.nodeNodeBetweenLayers':'84'}});
 const imageFor:Record<string,string>={purpose:artwork.images.purpose,approval:artwork.images.approval,exact:artwork.images.exact,transferKind:artwork.images.transfer,gateway:artwork.images.freshness,released:financial.images.payment};
 const diagram=composeDiagram({...context,model},specification,(node,ctx)=>{
  const id=key(node.sourceName!),failed=['purpose','joint','refused'].includes(id),color=failed?'#ba514b':id==='host'?'#a8772b':'#56716d';
  const label=node.label??id,uri=imageFor[id];
  const picture=uri?`<image href="${uri}" width="160" height="106" preserveAspectRatio="xMidYMid meet"/>`:id==='refused'?'<path d="M56 5h48l30 30v42l-30 25H56L26 77V35z" fill="#fff0ec" stroke="#ba514b" stroke-width="3"/><path d="m57 30 46 46m0-46L57 76" stroke="#ba514b" stroke-width="8" stroke-linecap="round"/>':`<g transform="translate(40 8)">${ctx.glyph(id==='host'?'registrar':'gate').replace('<svg ','<svg width="80" height="80" ')}</g>`;
  return `<g data-defense-component="${id}" data-observed-state="${status(id)}">${picture}<text data-text-line x="80" y="131" text-anchor="middle" font-size="14" font-weight="650" fill="#263845">${ctx.text(label)}</text><rect x="0" y="146" width="160" height="25" rx="12" fill="${failed?'#fff0ec':id==='host'?'#fff6e6':'#f0f4f3'}" stroke="${color}"/><text data-text-line x="80" y="163" text-anchor="middle" font-size="13" font-weight="700" fill="${color}">${status(id)}</text></g>`;
 });
 let markup=diagram.markup.replace('<svg ','<svg data-flow-observation="deployment_refused" ');
 const definitions='<pattern id="defense-grid" width="18" height="18" patternUnits="userSpaceOnUse"><circle cx="1" cy="1" r=".8" fill="#d8e2df"/></pattern><filter id="defense-shadow" x="-20%" y="-20%" width="140%" height="160%"><feDropShadow dx="0" dy="4" stdDeviation="4" flood-color="#243b35" flood-opacity=".08"/></filter><marker id="defense-red-port" viewBox="0 0 10 10" refX="5" refY="5" markerWidth="6" markerHeight="6"><circle cx="5" cy="5" r="3" fill="white" stroke="#ba514b" stroke-width="2"/></marker><marker id="defense-red-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M1 1L9 5L1 9" fill="none" stroke="#ba514b" stroke-width="2"/></marker>';
 markup=markup.replace('<defs>','<defs>'+definitions).replace('<g class="scene-groups">','<rect width="100%" height="100%" fill="url(#defense-grid)"/><g class="scene-groups">');
 const styles:string[]=[];
 for(const edge of model.relations){
  const active=byId.get(edge.src)==='purpose'||byId.get(edge.src)==='joint'&&byId.get(edge.dst)==='refused';
  markup=markup.replace(`data-scene-edge="${context.text(edge.id)}"`,`data-scene-edge="${context.text(edge.id)}" data-flow-state="${active?'refused':'required-inactive'}"`);
  styles.push(`[data-scene-edge="${edge.id}"]>.scene-edge{stroke:${active?'#ba514b':'#a6b6b2'};stroke-width:${active?3.5:1.6};stroke-dasharray:${active?'none':'6 5'};${active?'marker-start:url(#defense-red-port)!important;marker-end:url(#defense-red-arrow)!important;':''}}`);
 }
 return{markup:`<section class="defense-flow" data-surface="rectangle" data-flow-observation="deployment_refused">${markup}</section>`,css:diagram.css+styles.join('\n')+`.defense-flow{position:relative;z-index:2;margin:24px 0;background:#f8fbfa;border:1px solid #d9e5e0;border-radius:18px;padding:16px}.defense-flow .scene-frame{rx:14;stroke:#c5d5cf;filter:url(#defense-shadow)}.defense-flow [data-role="counter"]>.scene-frame{fill:#fffafa;stroke:#ba514b;stroke-width:2.3}.defense-flow [data-role="pending"]{opacity:.5}.defense-flow .scene-label{display:none}.defense-flow .scene-copy{font-family:Inter,sans-serif}`};
}
