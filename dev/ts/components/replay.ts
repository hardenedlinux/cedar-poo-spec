// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import {composeHeading,type FigureContext} from '@deterministic-engineering/render';
import {captureArtwork} from './artwork';
import {repositoryPath} from '../sources';
const path='dev/.generated/binance2026-metadata.json';
const laneIds=['bypass-countermodel','guarded-clean','guarded-prior'] as const;
const count=v.pipe(v.number(),v.integer(),v.minValue(0));
const State=v.object({signer_reachable:v.boolean(),signing_intents:count,paused:v.boolean(),delegated:v.boolean(),delegated_uses:count,settled:v.boolean(),refused:count,unknown:v.boolean()});
const Stage=v.object({id:v.string(),title:v.string(),basis:v.picklist(['reported','assumed','probe']),source:v.nullable(count),at_utc:v.nullable(v.string()),limitation:v.string()});
const Lane=v.object({id:v.picklist(laneIds),frames:v.array(v.object({stage:v.string(),state:State}))});
const ReplaySchema=v.object({
 provenance:v.object({metadata:v.object({id:v.literal('binance-2026-disclosed-chain-replay'),disclosures:v.array(v.object({url:v.string()}))}),ancestors:v.array(v.object({id:v.string()}))}),
 legitimate_once:v.literal(true),stages:v.array(Stage),lanes:v.array(Lane)
});
const Schema=v.object({replay:ReplaySchema});
export async function captureReplay(root:string){
 const raw=await readFile(await repositoryPath(root,path),'utf8'),data=v.parse(Schema,JSON.parse(raw)).replay;
 const ids=data.stages.map(stage=>stage.id);
 if(!ids.length||new Set(ids).size!==ids.length)throw new Error('Replay requires unique, nonempty stages');
 if(data.lanes.map(lane=>lane.id).join()!==laneIds.join())throw new Error('Replay must retain all three ordered lanes');
 for(const lane of data.lanes)if(lane.frames.map(frame=>frame.stage).join()!==ids.join())throw new Error('Replay lane omitted or reordered an actual stage');
 for(const stage of data.stages){
  if(stage.basis==='reported'&&(stage.source===null||stage.source>=data.provenance.metadata.disclosures.length))throw new Error('Reported stage needs its declared disclosure');
  if(stage.basis!=='reported'&&(stage.source!==null||stage.at_utc!==null))throw new Error('Synthetic stage cannot acquire historical attribution');
 }
 if(data.provenance.ancestors[0]?.id!=='binance-2026-10-29')throw new Error('Replay must retain the actual incident parent');
 const [doors,signer]=await Promise.all([
  captureArtwork(root,'dev/assets/financial/artwork.json',['purpose','approval'] as const,'dev/assets/financial/defense'),
  captureArtwork(root,'dev/assets/financial/artwork.json',['signer'] as const,'dev/assets/financial/binance')
 ]);
 return{images:{...doors.images,...signer.images},binaries:{...doors.binaries,...signer.binaries},...data,sources:{...doors.sources,...signer.sources,[path]:raw}};
}
export type Replay=Awaited<ReturnType<typeof captureReplay>>;
/** Every checkpoint is the real Lean fold's summary, not a TS-authored verdict. */
export function composeReplay(context:FigureContext,replay:Replay){
 const notes:ReturnType<typeof composeHeading>[]=[];
 const h=(text:string,role='note')=>{const value=composeHeading(context,{text,role});notes.push(value);return value.markup;};
 const lines=(text:string,limit=34)=>{let line='',markup='';for(const word of text.split(' ')){if(line&&line.length+word.length+1>limit){markup+=h(line,'heading');line=word;}else line+=(line?' ':'')+word;}return markup+(line?h(line,'heading'):'');};
 const names={'bypass-countermodel':'Unchecked relay countermodel','guarded-clean':'Guarded · no prior exposure','guarded-prior':'Guarded · prior exposure'};
 const imageIds={'bypass-countermodel':'purpose','guarded-clean':'approval','guarded-prior':'signer'} as const;
 const colors={'bypass-countermodel':'#ba514b','guarded-clean':'#167d78','guarded-prior':'#b07b27'};
 const headers=replay.lanes.map(lane=>`<section class="replay-lane" data-surface="rectangle">${h(names[lane.id],'heading')}<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-replay-lane="${lane.id}" width="300" height="180" viewBox="0 0 300 180"><image href="${replay.images[imageIds[lane.id]]}" width="300" height="180" preserveAspectRatio="xMidYMid meet"/></svg>${h(lane.id==='bypass-countermodel'?'Deliberately violates complete mediation':lane.id==='guarded-clean'?'Same attacker powers; checked writer':'Prior signed payment + delegation supplied')}</section>`).join('');
 const basisNames={reported:'REPORTED CONTEXT',assumed:'INITIAL ASSUMPTION',probe:'SYNTHETIC PROBE'};
 const rows=replay.stages.map((stage,index)=>{
  const cells=replay.lanes.map(lane=>{
   const state=lane.frames[index]!.state,previous=index?lane.frames[index-1]!.state:undefined;
   const color=colors[lane.id],newIntents=state.signing_intents-(previous?.signing_intents??0);
   const activity=state.delegated_uses-(previous?.delegated_uses??0),settled=state.settled&&!previous?.settled;
   const tick=settled?'<path d="m251 73 5 5 10-12" stroke="#426f9a" stroke-width="3" fill="none"/>':'';
   return `<article class="replay-cell" data-surface="rectangle"><svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-replay-checkpoint="${context.text(stage.id)}" data-lane="${lane.id}" data-signing-intents="${state.signing_intents}" data-delegated="${state.delegated}" data-settled="${state.settled}" width="300" height="108" viewBox="0 0 300 108" role="img" aria-label="${context.text(names[lane.id]+' at '+stage.title)}"><path d="M9 0v100m-4-6 4 6 4-6" stroke="${color}" stroke-width="2" fill="none"/><circle cx="9" cy="22" r="5" fill="white" stroke="${color}" stroke-width="2"/><path d="M31 30a7 7 0 1 0 0-14 7 7 0 0 0 0 14m7-7h18v6h-6v6h-5v-6" stroke="${color}" stroke-width="2" fill="none"/><text data-text-line x="70" y="32" font-size="27" font-weight="700" fill="${newIntents?'#ba514b':color}">${state.signing_intents}</text><text data-text-line x="105" y="30" font-size="14" fill="#263845">NEW SIGNING INTENTS</text><rect x="28" y="44" width="245" height="23" rx="10" fill="${state.delegated?'#fff2cf':'#eff5f2'}" stroke="${state.delegated?'#b07b27':'#b5c7c1'}"/><text data-text-line x="39" y="60" font-size="13" fill="#3c4f4b">${state.delegated?'DELEGATION LIVE':'NO LIVE DELEGATION'}</text>${tick}<text data-text-line x="29" y="90" font-size="13" fill="${activity?'#a16c18':'#426f9a'}">${activity?'DELEGATED ACTIVITY OBSERVED':settled?'LATE SETTLEMENT OBSERVED':state.paused?'PAUSE RETAINED':state.signer_reachable?'SIGNER NETWORK REACHED':'ACQUISITION / CONTEXT'}</text></svg></article>`;
  }).join('');
  const basis=`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" data-replay-stage="${context.text(stage.id)}" data-claim-basis="${stage.basis}" width="280" height="25" viewBox="0 0 280 25"><text data-text-line x="0" y="18" font-size="13" font-weight="700" fill="${stage.basis==='reported'?'#526c78':stage.basis==='assumed'?'#b07b27':'#76618b'}">${basisNames[stage.basis]}</text></svg>`;
  return `<div class="replay-stage">${h(String(index+1).padStart(2,'0'),'classification')}${lines(stage.title)}${basis}${stage.at_utc?h(stage.at_utc):''}</div>${cells}`;
 }).join('');
 return{markup:`<section class="differential-replay">${h('One disclosed chain. Three explicit starting conditions.','heading')}${h('Cumulative signing intents are model outputs, not real signatures. Settlement and delegated activity use separate channels.')}
 <div class="replay-grid"><div>${h('CHECKPOINT','classification')}${h('Every row retains its provenance')}</div>${headers}${rows}</div>
 <aside class="replay-scope" data-surface="rectangle">${h('POSITIVE CONTROL · LEGITIMATE PAYMENT DISPATCHES ONCE','classification')}${h('Guarded lanes do not pass by denying every payment. The original valid signer control succeeds once; replay is refused.')}${h('XRP / SOL / OP / BTC amounts are disclosed context. This replay does not implement their native codecs, an EVM, malware or undisclosed AI exploitation.')}</aside></section>`,css:notes.map(note=>note.css).join('\n')+`.differential-replay{margin:22px 0}.replay-grid{display:grid;grid-template-columns:1.1fr repeat(3,minmax(0,1fr));gap:10px;align-items:stretch;margin:20px 0}.replay-lane{border:1px solid #c3d3cc;border-radius:12px;background:#f8fbf9;padding:12px}.replay-lane>svg{display:block;max-width:100%;height:auto}.replay-stage{padding:12px 8px;border-bottom:1px solid #d7e1dd;align-self:center}.replay-stage>svg{display:block;margin:3px 0}.replay-cell{border:1px solid #d7e1dd;border-radius:10px;padding:8px;background:#fff;display:flex;align-items:center;justify-content:center}.replay-cell>svg{display:block;max-width:100%;height:auto}.replay-scope{padding:18px;border:2px dashed #b07b27;border-radius:12px;background:#fff8e9;margin:20px 0}`};
}
