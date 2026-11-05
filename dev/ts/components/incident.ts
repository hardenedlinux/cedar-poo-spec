// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import {composeHeading,type FigureContext} from '@deterministic-engineering/render';
import {repositoryPath} from '../sources';
import {captureArtwork} from './artwork';
const ids=['endpoint','ai-token','deployment','signer'] as const;
const manifestPath='dev/assets/financial/binance/storyboard.json',metadataPath='dev/.generated/binance2026-metadata.json';
const Metadata=v.object({metadata:v.object({id:v.literal('binance-2026-10-29'),kind:v.literal('reported-incident'),event:v.object({starts_on:v.string(),timezone:v.string()}),disclosures:v.array(v.object({publisher:v.string(),url:v.string(),published_on:v.string(),status:v.literal('preliminary')}))})});
const Manifest=v.object({formatVersion:v.literal(1),assets:v.array(v.object({id:v.picklist(ids),path:v.string(),sha256:v.string()}))});
export interface IncidentStory {
 readonly images:Readonly<Record<typeof ids[number],string>>;
 readonly provenance:v.InferOutput<typeof Metadata>;
 readonly defense:{readonly deployment_refused:boolean;readonly valid_transfer_released:boolean};
 readonly sources:Readonly<Record<string,string>>;
 readonly binaries:Readonly<Record<string,string>>;
}
/** Lean publishes incident provenance; illustration originals remain independently byte-bound. */
export async function captureIncidentStory(root:string):Promise<IncidentStory>{
 const artwork=await captureArtwork(root,manifestPath,ids,'dev/assets/financial/binance');
 const metadata=await readFile(await repositoryPath(root,metadataPath),'utf8');
 const observed=v.parse(v.object({provenance:Metadata,defense:v.object({deployment_refused:v.boolean(),valid_transfer_released:v.boolean()})}),JSON.parse(metadata)),provenance=observed.provenance;
 if(!provenance.metadata.disclosures.length)throw new Error('Reported story requires its Lean disclosure source');
 return{...artwork,provenance,defense:observed.defense,sources:{...artwork.sources,[metadataPath]:metadata}};
}
/** A reported-story layer; it does not add SDK subjects or pretend to prove the publisher's facts. */
export function composeIncident(context:FigureContext,story:IncidentStory){
 const parts:ReturnType<typeof composeHeading>[]=[];
 const h=(text:string,role='note')=>{const part=composeHeading(context,{text,role});parts.push(part);return part.markup;};
 const lines=(value:string,limit=42)=>{let line='',out='';for(const word of value.split(' ')){if(line&&line.length+word.length+1>limit){out+=h(line);line=word;}else line+=(line?' ':'')+word;}return out+(line?h(line):'');};
 const phases=[
  {id:'endpoint',title:'1 · An attractive offer',action:'A malicious download compromises an engineer endpoint.',defense:'Host: protect endpoints and verify software origins. Cedar does not undo malware.'},
  {id:'ai-token',title:'2 · A foothold becomes access',action:'An internal AI tool helps lateral movement to other endpoints; a deployment token is stolen.',defense:'Zero Trust: internal reachability is not authority. The AI exploit itself is undisclosed.'},
  {id:'deployment',title:'3 · The wrong key opens a route',action:'Deployment authority leads through a container to the wallet-signing service.',defense:'Modeled refusal: a deployment purpose cannot release a payment signature.'},
  {id:'signer',title:'4 · The wallet is made to act',action:'Unauthorized signer use bypasses normal withdrawals; Ethereum delegation adds lasting exposure.',defense:'Require current approval for the exact transfer. This profile refuses delegation and arbitrary calldata.'}
 ] as const;
 const illustration=(id:typeof ids[number])=>`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-incident-scene="${id}" role="img" aria-label="Conceptual reported attack stage: ${id}" width="360" height="220" viewBox="0 0 360 220"><image href="${story.images[id]}" width="360" height="220" preserveAspectRatio="xMidYMid meet"/></svg>`;
 const arrow=(color:string)=>`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" width="54" height="22" viewBox="0 0 54 22"><path d="M2 11H49m-10-8 10 8-10 8" fill="none" stroke="${color}" stroke-width="3"/></svg>`;
 const stages=phases.map(phase=>`<article class="incident-act" data-surface="rectangle">${h(phase.title,'heading')}${illustration(phase.id)}<div class="reported-action">${lines(phase.action)}</div><div class="defense-answer">${lines(phase.defense)}</div></article>`).join('');
 const gates=[['Identity','Real workload + current release'],['Purpose','Signing role, never deployment'],['Approval','Independent current payment review'],['Exact effect','Same transfer + nonce + gateway']];
 const gateBoard=gates.map(([title,detail],index)=>`<div class="signing-gate" data-surface="rectangle">${h(title!,'heading')}${lines(detail!,32)}</div>${index<gates.length-1?`<div class="gate-arrow">${arrow('#167d78')}</div>`:''}`).join('');
 const source=story.provenance.metadata.disclosures[0]!;
 const legend=h('CORAL: reported attack path · TEAL: modeled checks · AMBER: Host or on-chain obligations','classification');
 return{markup:`<section class="incident-story" data-incident-story="binance-2026">${h('One compromised laptop. A path to the signing service.','heading')}${legend}<div class="reported-route">${h('REPORTED SEQUENCE → ENDPOINT → INTERNAL AI / OTHER ENDPOINTS → DEPLOYMENT → SIGNER','classification')}</div><div class="incident-acts">${stages}</div><section class="delegation-timeline" data-surface="rectangle">${h('Why pressing pause does not remove a delegated key','heading')}<div class="delegation-states"><div>${h('LOCAL PAUSE','classification')}${h('No new modeled signing')}${h('Existing delegation remains')}</div><div>${arrow('#b07b27')}</div><div>${h('CLEARING SUBMITTED','classification')}${h('A request is not finality')}${h('Existing delegation remains')}</div><div>${arrow('#b07b27')}</div><div>${h('EXACT VERIFIED FINALIZED CLEAR','classification')}${h('Same wallet + network + nonce')}${h('Only then remove modeled exposure')}</div></div></section>${lines(`Source: ${source.publisher}, ${source.published_on}; incident begins ${story.provenance.metadata.event.starts_on} ${story.provenance.metadata.event.timezone}. Preliminary findings. Scenes are explanatory illustrations, not forensic screenshots.`,110)}${h('Now put that stolen deployment key through the modeled defense','heading')}</section>`,css:parts.map(part=>part.css).join('\n')+`.incident-story{margin:22px 0}.incident-acts{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:16px;margin:12px 0 24px}.incident-act{position:relative;z-index:2;border:2px solid #ba514b;border-radius:10px;padding:12px;background:#fff}.incident-act>svg[data-incident-scene]{display:block;max-width:100%;height:auto;margin:10px 0}.incident-act>svg[data-heading-role]{margin:0}.reported-action{min-height:92px}.defense-answer{border-top:2px solid #167d78;padding-top:12px;margin-top:12px}.reported-route{padding:12px 0;color:#ba514b}.last-gate{position:relative;z-index:2;padding:20px;border:2px solid #167d78;border-radius:10px;background:#eef7f3}.signing-gates{display:grid;grid-template-columns:1fr 54px 1fr 54px 1fr 54px 1fr;align-items:center;gap:8px;margin:18px 0}.signing-gate{position:relative;z-index:2;border:1px solid #167d78;border-radius:8px;padding:12px;background:white;min-height:92px}.gate-arrow svg{display:block}.delegation-timeline{position:relative;z-index:2;border:1px solid #b07b27;border-radius:10px;background:#fff8e9;padding:20px;margin:22px 0}.delegation-states{display:grid;grid-template-columns:1fr 54px 1fr 54px 1.3fr;gap:14px;align-items:center;margin-top:16px}.delegation-states>div>svg{display:block;margin:5px 0}`};
}
