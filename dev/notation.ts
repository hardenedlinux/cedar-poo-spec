// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import * as v from 'valibot';
import {composeHeading,composeDiagram,modelDiagram,type FigureContext,type FigureComposer,type FigureModel} from '@deterministic-engineering/render';
import type {ProofMap,ProofCard} from './proofs';
type FigureComposition=ReturnType<FigureComposer>;
const text=v.pipe(v.string(),v.minLength(1));
const Group=v.strictObject({title:text,subjects:v.pipe(v.array(text),v.minLength(1)),columns:v.optional(v.pipe(v.number(),v.integer(),v.minValue(1),v.maxValue(3)),1)});
const Activity=v.strictObject({entry:v.optional(text),terminals:v.optional(v.array(text)),decisions:v.optional(v.array(text)),stages:v.optional(v.array(Group))});
const Authored=v.object({notation:v.picklist(['components','catalogue','matrix','bars','assurance','workflow','swimlanes','tasks']),groups:v.optional(v.array(Group)),activity:v.optional(Activity),columns:v.optional(v.pipe(v.number(),v.integer(),v.minValue(1),v.maxValue(3)),2)});
type Grouping=v.InferOutput<typeof Group>;
export interface Notation {
 readonly notation:v.InferOutput<typeof Authored>['notation'];
 readonly groups:readonly Grouping[];
 readonly activity?:{entry?:string;terminals:readonly string[];decisions:readonly string[];stages:readonly Grouping[]};
 readonly columns:number;
 readonly order:readonly string[];
 readonly icons:Readonly<Record<string,string>>;
 readonly metrics:Readonly<Record<string,number>>;
 readonly proofRoles:Readonly<Record<string,ProofCard['role']>>;
 readonly proofDependencies:readonly string[];
}
/** Reading groups are presentation only. SDK identities and edges stay intact. */
export function bindNotation(value:unknown,mapping:Readonly<Record<string,string>>,model:FigureModel,
 icons:Readonly<Record<string,string>>,proofs?:ProofMap,metrics:Readonly<Record<string,number>>={}):Notation {
 const source=v.parse(Authored,value),order=Object.values(mapping);
 if(new Set(order).size!==model.subjects.length||model.subjects.some(node=>!order.includes(node.id)))throw new Error('Notation needs the complete SDK subject set');
 const groups=(source.groups??[]).map(group=>({...group,subjects:group.subjects.map(id=>{
  if(!Object.hasOwn(mapping,id))throw new Error('Unknown reading-group subject: '+id);return mapping[id]!;
 })}));
 if(['components','catalogue','assurance','swimlanes','tasks'].includes(source.notation)){
  const assigned=groups.flatMap(group=>group.subjects);
  if(new Set(assigned).size!==assigned.length||assigned.length!==order.length-(source.notation==='tasks'?1:0)||source.notation==='tasks'&&assigned.includes(mapping[source.activity?.entry??'']!))throw new Error('Every SDK subject needs exactly one reading group');
 }else if(groups.length)throw new Error('This notation does not use reading groups');
 if(['catalogue','bars'].includes(source.notation)&&model.relations.length)throw new Error('Inventory notation cannot discard model relations');
 const resolve=(id:string)=>{if(!Object.hasOwn(mapping,id))throw new Error('Unknown activity subject: '+id);return mapping[id]!;};
 const temporal=['workflow','swimlanes','tasks'].includes(source.notation);
 if(temporal&&!source.activity)throw new Error('Activity notation requires declared semantics');
 if(!temporal&&source.activity)throw new Error('Static notation cannot claim activity semantics');
 const activity=source.activity?{entry:source.activity.entry?resolve(source.activity.entry):undefined,terminals:(source.activity.terminals??[]).map(resolve),decisions:(source.activity.decisions??[]).map(resolve),stages:(source.activity.stages??[]).map(group=>({...group,subjects:group.subjects.map(resolve)}))}:undefined;
 if(temporal){
  const outgoing=(id:string)=>model.relations.filter(edge=>edge.src===id);
  const incoming=(id:string)=>model.relations.filter(edge=>edge.dst===id);
  if(model.relations.some(edge=>!order.includes(edge.src)||!order.includes(edge.dst)))throw new Error('Unbound activity endpoint');
  const visit=(id:string,path:Set<string>,seen:Set<string>)=>{if(path.has(id))throw new Error('Cyclic activity');if(seen.has(id))return;seen.add(id);for(const edge of outgoing(id))visit(edge.dst,new Set([...path,id]),seen);};
  if(source.notation==='swimlanes'){
   const staged=activity!.stages.flatMap(stage=>stage.subjects);
   if(staged.length!==order.length||new Set(staged).size!==order.length)throw new Error('Each activity needs exactly one stage');
   const rank=new Map(activity!.stages.flatMap((stage,index)=>stage.subjects.map(id=>[id,index] as const)));
   if(model.relations.some(edge=>rank.get(edge.src)!>=rank.get(edge.dst)!))throw new Error('Handoff must advance the declared stage');
   if(activity!.entry||activity!.terminals.length||activity!.decisions.length)throw new Error('Swimlanes use stages, not workflow outcomes');
  }else{
   if(!activity!.entry||activity!.stages.length)throw new Error('Dependency notation needs one entry and no stages');
   if(incoming(activity!.entry).length)throw new Error('Activity entry cannot have an incoming edge');
   const seen=new Set<string>();visit(activity!.entry,new Set(),seen);
   if(seen.size!==order.length)throw new Error('Unreachable activity subject');
   if(source.notation==='workflow'){
    if(!activity!.terminals.length||new Set(activity!.terminals).size!==activity!.terminals.length||new Set(activity!.decisions).size!==activity!.decisions.length)throw new Error('Workflow needs distinct declared outcomes');
    for(const id of order){
     const edges=outgoing(id);
     if(activity!.terminals.includes(id)){if(edges.length)throw new Error('Workflow outcome cannot continue');}
     else if(activity!.decisions.includes(id)){
      if(edges.length<2||edges.some(edge=>!edge.label.trim())||new Set(edges.map(edge=>edge.label)).size!==edges.length)throw new Error('Decision needs distinct labelled alternatives');
     }else if(edges.length!==1)throw new Error('Action needs exactly one successor');
    }
   }else{
    if(activity!.terminals.length||activity!.decisions.length)throw new Error('Task requirements are conjunctive, not workflow alternatives');
    if(order.some(id=>id!==activity!.entry&&incoming(id).length!==1)||model.relations.some(edge=>edge.label!=='requires'))throw new Error('Task decomposition needs single-parent requires edges');
   }
  }
 }
 const values:Record<string,number>={};
 for(const[id,count]of Object.entries(metrics)){
  if(!Object.hasOwn(mapping,id)||!Number.isSafeInteger(count)||count<0)throw new Error('Invalid captured catalog metric');values[mapping[id]!]=count;
 }
 if(source.notation==='bars'&&order.some(id=>!Object.hasOwn(values,id)))throw new Error('Missing captured catalog metric');
 if(['workflow','tasks'].includes(source.notation)&&(!proofs||model.subjects.some(node=>!proofs.cards.some(card=>card.id===node.sourceName))))throw new Error('Activity requires captured Lean declarations');
 const roles:Record<string,ProofCard['role']>={},symbols=new Map<string,string>();
 if(source.notation==='assurance'){
  if(!proofs)throw new Error('Assurance notation requires the SDK proof map');
  for(const node of model.subjects){const card=proofs.cards.find(card=>card.id===node.sourceName);if(!card)throw new Error('Unbound proof role: '+node.id);roles[node.id]=card.role;symbols.set(node.id,card.symbol);}
 }
 const proofDependencies=model.relations.filter(edge=>proofs?.uses.some(use=>use.dependency===symbols.get(edge.src)&&use.target===symbols.get(edge.dst))).map(edge=>edge.id);
 return{notation:source.notation,groups,activity,columns:source.columns,order,icons,metrics:values,proofRoles:roles,proofDependencies};
}
const roleNames:Record<ProofCard['role'],string>={Definition:'DEFINITION',KernelLaw:'KERNEL THEOREM',KernelCounterexample:'PROVED COUNTEREXAMPLE',HostPremise:'HOST PREMISE'};
const wrap=(value:string,limit=52):string[]=>{
 const lines:string[]=[];let line='';
 for(const word of value.split(/\s+/)){if(line&&line.length+word.length+1>limit){lines.push(line);line=word;}else line+=(line?' ':'')+word;}
 if(line)lines.push(line);return lines;
};
/** Native vector annotations and declared surfaces also support non-graph views. */
export function composeNotation(context:FigureContext):FigureComposition {
 const model=context.model;if(!model)throw new Error('Missing SDK notation model');
 const data=context.presentation as Notation,parts:FigureComposition[]=[];
 const heading=(value:string,role='note',glyph?:string)=>{
  const part=composeHeading(context,{text:value,role,...(glyph?{glyph}:{})});parts.push(part);return part.markup;
 };
 const lines=(value:string,role='note',limit=52)=>wrap(value,limit).map(line=>heading(line,role)).join('');
 const subject=(id:string)=>{const node=model.subjects.find(node=>node.id===id);if(!node)throw new Error('Unknown notation subject: '+id);return node;};
 const title=(id:string)=>(subject(id).label??id).split('\n')[0]!;
 const relation=(edge:FigureModel['relations'][number])=>`<section class="basis" data-relation="${context.text(edge.id)}">${heading(data.proofDependencies.includes(edge.id)?'CHECKED LEMMA DEPENDENCY':'READING RELATION','classification')}${lines(title(edge.src))}${lines(edge.label)}</section>`;
 const card=(id:string,assurance=false)=>{
  const node=subject(id),[name,...body]=(node.label??id).split('\n'),role=data.proofRoles[id];
  return `<article data-node="${context.text(id)}" data-surface="rectangle" class="subject"${role?` data-proof-role="${role}"`:''}>${role?heading(roleNames[role],'classification'):''}${heading(name!,'heading',data.icons[id])}${body.map(line=>lines(line)).join('')}${assurance?model.relations.filter(edge=>edge.dst===id).map(relation).join(''):''}</article>`;
 };
 const groups=(assurance=false)=>`<section class="reading-groups ${data.notation}" style="grid-template-columns:repeat(${data.columns},minmax(0,1fr))">${data.groups.map(group=>`<section class="reading-group" data-surface="rectangle">${heading(group.title,'heading')}<div class="members" style="grid-template-columns:repeat(${group.columns},minmax(0,1fr))">${group.subjects.map(id=>card(id,assurance)).join('')}</div></section>`).join('')}</section>`;
 let markup:string;
 if(data.notation==='workflow'){
  const directed={...model,relations:model.relations.map(edge=>({...edge,srcArrow:'none' as const,dstArrow:'arrow' as const}))};
  return composeDiagram({...context,model:directed},modelDiagram(directed,{icons:data.icons,options:{'elk.direction':'DOWN','elk.algorithm':'layered','elk.spacing.nodeNode':'45','elk.layered.spacing.nodeNodeBetweenLayers':'65'}}));
 }else if(data.notation==='swimlanes'){
  const laneFor=(id:string)=>data.groups.find(group=>group.subjects.includes(id))!.title;
  markup=`<table class="lanes"><thead><tr><th data-surface="rectangle">${heading('CALL ORDER','classification')}</th>${data.groups.map(group=>`<th data-surface="rectangle">${heading(group.title,'heading')}</th>`).join('')}</tr></thead><tbody>${data.activity!.stages.map((stage,index)=>`<tr><th data-surface="rectangle">${heading(String(index+1).padStart(2,'0'),'classification')}${lines(stage.title,'note',25)}</th>${data.groups.map(group=>`<td data-surface="rectangle">${stage.subjects.filter(id=>group.subjects.includes(id)).map(id=>card(id)+model.relations.filter(edge=>edge.src===id).map(edge=>`<section class="handoff" data-relation="${context.text(edge.id)}" data-from="${context.text(id)}" data-to="${context.text(edge.dst)}">${heading('NEXT: '+laneFor(edge.dst),'classification')}${lines(edge.label)}</section>`).join('')).join('')}</td>`).join('')}</tr>`).join('')}</tbody></table>`;
 }else if(data.notation==='tasks'){
  const requirement=(id:string)=>{const edge=model.relations.find(edge=>edge.dst===id)!;return `<div class="task-requirement" data-relation="${context.text(edge.id)}">${card(id)}</div>`;};
  markup=`<section class="task-board">${data.groups.map((group,index)=>`<section class="task-zone" data-surface="rectangle"><div class="task-scene">${context.glyph(data.icons[group.subjects[0]!]!)}</div>${heading(String.fromCharCode(65+index)+' · '+group.title,'heading')}<div class="task-parts" style="grid-template-columns:repeat(${group.columns},minmax(0,1fr))">${group.subjects.map(requirement).join('')}</div></section>`).join('')}</section><div class="task-join">${heading('ALL REQUIRED TOGETHER · ONE DECIDING VIEW','classification')}</div><section class="task-result" data-surface="rectangle"><div class="task-scene">${context.glyph(data.icons[data.activity!.entry!]!)}</div>${card(data.activity!.entry!)}</section>`;
 }else if(data.notation==='components'){
  markup=groups()+heading('Declared component relationships','heading')+`<table class="interface-table"><thead><tr><th data-surface="rectangle">${heading('SOURCE','classification')}</th><th data-surface="rectangle">${heading('RELATED COMPONENT','classification')}</th><th data-surface="rectangle">${heading('RELATIONSHIP','classification')}</th></tr></thead><tbody>${model.relations.map(edge=>`<tr data-relation="${context.text(edge.id)}"><td data-surface="rectangle">${lines(title(edge.src),'note',44)}</td><td data-surface="rectangle">${lines(title(edge.dst),'note',44)}</td><td data-surface="rectangle">${lines(edge.label,'note',50)}</td></tr>`).join('')}</tbody></table>`;
 }else if(data.notation==='catalogue')markup=groups();
 else if(data.notation==='assurance')markup=groups(true);
 else if(data.notation==='matrix'){
  markup=`<table class="responsibilities"><thead><tr><th data-surface="rectangle">${heading('LAYER','classification')}</th><th data-surface="rectangle">${heading('RESPONSIBILITY','classification')}</th><th data-surface="rectangle">${heading('DECLARED RELATIONSHIPS','classification')}</th></tr></thead><tbody>${data.order.map(src=>{const outgoing=model.relations.filter(edge=>edge.src===src);return `<tr><th data-node="${context.text(src)}" data-surface="rectangle">${lines(title(src),'heading',32)}</th><td data-surface="rectangle">${(subject(src).label??src).split('\n').slice(1).map(line=>lines(line,'note',48)).join('')}</td><td data-surface="rectangle">${outgoing.length?outgoing.map(edge=>`<section class="related" data-relation="${context.text(edge.id)}" data-from="${context.text(src)}" data-to="${context.text(edge.dst)}">${lines(title(edge.dst),'heading',42)}${lines(edge.label,'note',48)}</section>`).join(''):heading('—')}</td></tr>`;}).join('')}</tbody></table>`;
 }else if(data.notation==='bars'){
  const maximum=Math.max(1,...data.order.map(id=>data.metrics[id]!)),height=data.order.length*92+70;
  markup=`<svg data-vector-surface xmlns="http://www.w3.org/2000/svg" role="img" aria-label="Native catalog entries by transport form" viewBox="0 0 1100 ${height}" width="100%" class="catalog-bars"><line x1="440" y1="20" x2="440" y2="${height-38}" stroke="var(--border)"/>${data.order.map((id,index)=>{const value=data.metrics[id]!,y=30+index*92;return `<g data-node="${context.text(id)}"><text x="0" y="${y}" font-size="17" fill="var(--ink)">${(subject(id).label??id).split('\n').slice(0,1).map((line,lineIndex)=>`<tspan x="0" dy="${lineIndex?19:0}"${lineIndex?' font-size="14"':''}>${context.text(line)}</tspan>`).join('')}</text><rect x="440" y="${y+3}" width="${value/maximum*550}" height="26" rx="3" fill="var(--accent)"/><text x="1010" y="${y+24}" font-size="18" fill="var(--ink)">${value}</text></g>`;}).join('')}<text x="440" y="${height-8}" font-size="14" fill="var(--muted)">0</text><text x="990" y="${height-8}" text-anchor="end" font-size="14" fill="var(--muted)">${maximum} entries</text></svg>`;
 }else throw new Error('Unknown declared notation');
 return{markup,css:parts.map(part=>part.css).join('\n')+`
.lanes{width:100%;table-layout:fixed;border-spacing:0;margin:20px 0}.lanes th,.lanes td{border:1px solid var(--border);padding:12px;vertical-align:top;background:var(--surface)}.lanes th{background:var(--tint);text-align:left}.lanes th:first-child{width:17%}.handoff{margin-top:12px;border-top:1px solid var(--border);padding-top:8px}.task-board{display:grid;grid-template-columns:1fr 1.6fr 1fr;gap:20px;margin:20px 0 0}.task-zone{border:1px solid var(--border);background:var(--tint);border-radius:12px;padding:20px}.task-zone:nth-child(2){background:var(--surface)}.task-scene{display:flex;align-items:center;justify-content:center;color:var(--accent);height:110px;margin:0 0 10px}.task-scene>svg{width:104px;height:104px}.task-parts{display:grid;gap:12px;margin-top:18px}.task-parts .subject{padding:12px}.task-join{text-align:center;padding:18px 0}.task-result{display:flex;align-items:center;justify-content:center;gap:30px;border:2px solid var(--accent);border-radius:12px;background:var(--tint);padding:20px}.task-result .task-scene{height:auto;margin:0}.task-result .subject{border:0;background:none}.task-tree ul{list-style:none;padding-left:24px}.task-tree>ul{padding-left:0}.task-tree li{margin:12px 0}.task-children{display:grid;gap:16px;align-items:start}.task-tree .requirement{border-left:2px solid var(--accent);padding-left:14px}.reading-groups{display:grid;gap:20px;align-items:start}.reading-groups.components{grid-template-columns:repeat(2,minmax(0,1fr))}.reading-groups.catalogue{grid-template-columns:repeat(2,minmax(0,1fr))}.reading-groups.assurance{grid-template-columns:repeat(3,minmax(0,1fr))}.reading-group{border:1px solid var(--border);background:var(--tint);border-radius:8px;padding:16px}.members{display:grid;gap:12px;margin-top:10px;align-items:start}.subject,.interface{border:1px solid var(--border);background:var(--surface);border-radius:5px;padding:14px;min-width:0}.subject[data-proof-role="KernelLaw"]{border-color:var(--accent)}.subject[data-proof-role="KernelCounterexample"]{border-color:var(--secondary);background:var(--secondaryTint)}.subject[data-proof-role="HostPremise"]{border-color:var(--pending)}[data-heading-role="classification"] text{font-size:12px;fill:var(--muted);letter-spacing:.4px}.basis{margin-top:12px;padding-top:8px;border-top:1px solid var(--border)}.interfaces{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;margin:12px 0}.endpoints{display:grid;grid-template-columns:1fr 1fr;gap:12px}.interface-table,.responsibilities{width:100%;table-layout:fixed;border-spacing:0;margin:20px 0}.interface-table th,.interface-table td,.responsibilities th,.responsibilities td{border:1px solid var(--border);background:var(--surface);padding:12px;text-align:left;vertical-align:top}.interface-table th:first-child{width:30%}.responsibilities th:first-child{width:26%}.related+.related{margin-top:12px;padding-top:8px;border-top:1px solid var(--border)}.interface-table thead th,.responsibilities thead th{background:var(--tint)}.catalog-bars{display:block;margin:24px 0;font-family:inherit}`};
}
