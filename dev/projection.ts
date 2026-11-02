// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import * as v from 'valibot';
import type {FigureInput,FigureModel} from '@deterministic-engineering/render';
import {projectOpenSysMLView,type OpenSysMLCapture} from '@deterministic-engineering/render/opensysml';
const text=v.pipe(v.string(),v.minLength(1));
export const ProjectionSchema=v.object({sysml:v.strictObject({source:text,view:text,bindings:v.record(text,v.strictObject({name:text,icon:text}))})});
export type Bindings=v.InferOutput<typeof ProjectionSchema>['sysml']['bindings'];
/** SysML supplies identities/topology; D2 supplies captions/icons. Never substitute topology. */
export function bindView(author:FigureInput,capture:OpenSysMLCapture,bindings:Bindings,captions:Readonly<Record<string,string>>={}){
 const names=new Map(capture.rendering.nodes.map(node=>[node.name,node.id]));
 if(names.size!==capture.rendering.nodes.length)throw new Error('Ambiguous SDK source name');
 const labels:Record<string,string>={},icons:Record<string,string>={},mapping:Record<string,string>={};
 for(const[id,binding]of Object.entries(bindings)){
  const native=names.get(binding.name),subject=author.model?.subjects.find(node=>node.id===id);
  if(!native||!subject)throw new Error('Missing SDK / authored subject binding: '+id);
  mapping[id]=native;icons[native]=binding.icon;labels[native]=captions[id]??subject.label??subject.id;
 }
 if(new Set(Object.values(mapping)).size!==Object.keys(mapping).length)throw new Error('Multiple authored subjects bind one SDK identity');
 if(names.size!==Object.keys(mapping).length||author.model!.subjects.length!==names.size)throw new Error('Unbound SDK / D2 node');
 for(const id of Object.keys(captions))if(!Object.hasOwn(mapping,id))throw new Error('Unbound display caption');
 const native=projectOpenSysMLView(capture,{selection:author.view,layout:'reflow',labels}),used=new Set<string>();
 const relations:FigureModel['relations']=native.model.relations.map(edge=>{
  const candidates=author.model!.relations.filter(candidate=>mapping[candidate.src]===edge.src&&mapping[candidate.dst]===edge.dst);
  if(candidates.length!==1||used.has(candidates[0]!.id))throw new Error('SDK / D2 relation closure mismatch');
  used.add(candidates[0]!.id);return{...edge,label:candidates[0]!.label};
 });
 if(used.size!==author.model!.relations.length)throw new Error('SDK view omitted an authored relation');
 return{model:{subjects:native.model.subjects,relations},trace:native.trace,icons,mapping};
}
