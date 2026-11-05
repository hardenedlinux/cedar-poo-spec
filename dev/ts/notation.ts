// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import * as v from 'valibot';
import {composeHeading,composeDiagram,modelDiagram,type FigureContext,type FigureComposer,type FigureModel} from '@deterministic-engineering/render';
import type {ProofMap,ProofCard} from './proofs';
type FigureComposition=ReturnType<FigureComposer>;
const text=v.pipe(v.string(),v.minLength(1));
const Group=v.strictObject({title:text,icon:v.optional(text),subjects:v.pipe(v.array(text),v.minLength(1)),columns:v.optional(v.pipe(v.number(),v.integer(),v.minValue(1),v.maxValue(5)),1)});
const Activity=v.strictObject({entry:v.optional(text),terminals:v.optional(v.array(text)),decisions:v.optional(v.array(text)),stages:v.optional(v.array(Group)),critical:v.optional(Group),direction:v.optional(v.picklist(['RIGHT','DOWN']))});
const Authored=v.object({notation:v.picklist(['components','catalogue','dependencies','bars','assurance','workflow','swimlanes','tasks']),groups:v.optional(v.array(Group)),activity:v.optional(Activity),columns:v.optional(v.pipe(v.number(),v.integer(),v.minValue(1),v.maxValue(4)),2)});
type Grouping=v.InferOutput<typeof Group>;
export interface Notation {
 readonly notation:v.InferOutput<typeof Authored>['notation'];
 readonly groups:readonly Grouping[];
 readonly activity?:{entry?:string;direction?:'RIGHT'|'DOWN';terminals:readonly string[];decisions:readonly string[];stages:readonly Grouping[];critical?:Grouping};
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
 const activity=source.activity?{direction:source.activity.direction,critical:source.activity.critical?{...source.activity.critical,subjects:source.activity.critical.subjects.map(resolve)}:undefined,entry:source.activity.entry?resolve(source.activity.entry):undefined,terminals:(source.activity.terminals??[]).map(resolve),decisions:(source.activity.decisions??[]).map(resolve),stages:(source.activity.stages??[]).map(group=>({...group,subjects:group.subjects.map(resolve)}))}:undefined;
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
   if(activity!.critical){
    const ranks=activity!.critical.subjects.map(id=>rank.get(id)!);
    if(new Set(ranks).size!==ranks.length||Math.max(...ranks)-Math.min(...ranks)+1!==ranks.length)throw new Error('Critical region needs contiguous unique stages');
   }
  }else{
   if(!activity!.entry||activity!.stages.length||activity!.critical)throw new Error('Dependency notation needs one entry and no stages');
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
export function composeNotation(context:FigureContext,illustrations?:ReadonlyMap<string,FigureComposition>):FigureComposition {
 const model=context.model;if(!model)throw new Error('Missing SDK notation model');
 const data=context.presentation as Notation,parts:FigureComposition[]=[];
 const heading=(value:string,role='note',glyph?:string)=>{
  const part=composeHeading(context,{text:value,role,...(glyph?{glyph}:{})});parts.push(part);return part.markup;
 };
 const lines=(value:string,role='note',limit=52)=>wrap(value,limit).map(line=>heading(line,role)).join('');
 const subject=(id:string)=>{const node=model.subjects.find(node=>node.id===id);if(!node)throw new Error('Unknown notation subject: '+id);return node;};
 const title=(id:string)=>(subject(id).label??id).split('\n')[0]!;
 const key=(id:string)=>{const group=data.groups.findIndex(group=>group.subjects.includes(id));return group<0?'':String.fromCharCode(65+group)+(data.groups[group]!.subjects.indexOf(id)+1);};
 const relation=(edge:FigureModel['relations'][number])=>`<section class="basis" data-relation="${context.text(edge.id)}" data-from="${context.text(edge.src)}" data-to="${context.text(edge.dst)}">${heading((data.proofDependencies.includes(edge.id)?'PROOF':'CONTEXT')+' '+key(edge.src)+' → '+key(edge.dst),'classification')}${lines(edge.label,'note',36)}</section>`;
 const card=(id:string,assurance=false)=>{
  const node=subject(id),[name,...body]=(node.label??id).split('\n'),role=data.proofRoles[id];
  return `<article data-node="${context.text(id)}" data-surface="rectangle" class="subject"${role?` data-proof-role="${role}"`:''}>${role?heading(roleNames[role],'classification'):''}${heading((assurance?key(id)+' · ':'')+name!,'heading',data.icons[id])}${illustrations?.has(node.sourceName!)?`<div class="component-miniature">${illustrations.get(node.sourceName!)!.markup}</div>`:''}${body.map(line=>lines(line)).join('')}${assurance?model.relations.filter(edge=>edge.dst===id).map(relation).join(''):''}</article>`;
 };
 const groups=(assurance=false)=>`<section class="reading-groups ${data.notation}" style="grid-template-columns:repeat(${data.columns},minmax(0,1fr))">${data.groups.map(group=>`<section class="reading-group" data-surface="rectangle"><header class="group-heading">${group.icon?`<div class="group-scene">${context.glyph(group.icon)}</div>`:''}<div>${lines(group.title,'heading',data.notation==='components'?25:40)}</div></header><div class="members" style="grid-template-columns:repeat(${group.columns},minmax(0,1fr))">${group.subjects.map(id=>card(id,assurance)).join('')}</div></section>`).join('')}</section>`;
 let markup:string;
 if(data.notation==='workflow'){
  const directed={...model,relations:model.relations.map(edge=>({...edge,srcArrow:'none' as const,dstArrow:'arrow' as const}))};
  return composeDiagram({...context,model:directed},modelDiagram(directed,{icons:data.icons,options:{'elk.direction':data.activity?.direction??'RIGHT','elk.algorithm':'layered','elk.spacing.nodeNode':'18','elk.layered.spacing.nodeNodeBetweenLayers':'24'}}));
 }else if(data.notation==='swimlanes'){
  const laneIndex=(id:string)=>data.groups.findIndex(group=>group.subjects.includes(id));
  const stageIndex=(id:string)=>data.activity!.stages.findIndex(stage=>stage.subjects.includes(id));
  const critical=data.activity!.critical;
  const scope=critical?{first:Math.min(...critical.subjects.map(stageIndex)),last:Math.max(...critical.subjects.map(stageIndex)),left:Math.min(...critical.subjects.map(laneIndex)),right:Math.max(...critical.subjects.map(laneIndex))}:undefined;
  const boundary=scope?`<div class="lane-critical" data-surface="rectangle" style="top:${14+90*scope.first}px;height:${(scope.last-scope.first+1)*90-8}px;left:calc(${scope.left*100/data.groups.length}% + 5px);right:calc(${(data.groups.length-1-scope.right)*100/data.groups.length}% + 5px)"><div class="critical-label">${heading(critical!.title,'classification')}</div></div>`:'';
  markup=`<section class="lane-headings" style="grid-template-columns:repeat(${data.groups.length},minmax(0,1fr))">${data.groups.map(group=>`<div class="lane-heading">${group.icon?`<div class="lane-person">${context.glyph(group.icon)}</div>`:''}${heading(group.title,'heading')}</div>`).join('')}</section><section class="lane-canvas">${boundary}<div class="lane-backgrounds" style="grid-template-columns:repeat(${data.groups.length},minmax(0,1fr))">${data.groups.map(()=>'<div data-surface="rectangle"></div>').join('')}</div><svg data-connections data-vector-surface xmlns="http://www.w3.org/2000/svg" class="lane-arrows">${model.relations.map(edge=>{const same=laneIndex(edge.src)===laneIndex(edge.dst);return `<path data-relation="${context.text(edge.id)}" data-from="${context.text(edge.src)}" data-to="${context.text(edge.dst)}" data-source-position="${same?'bottom':laneIndex(edge.src)<laneIndex(edge.dst)?'right':'left'}" data-target-position="${same?'top':laneIndex(edge.src)<laneIndex(edge.dst)?'left':'right'}"/>`;}).join('')}</svg><div class="lane-actions" style="grid-template-rows:repeat(${data.activity!.stages.length},72px);grid-template-columns:repeat(${data.groups.length},minmax(0,1fr))">${data.order.map(id=>`<div class="lane-operation" style="grid-column:${laneIndex(id)+1};grid-row:${stageIndex(id)+1}">${card(id)}</div>`).join('')}</div></section>`;
 }else if(data.notation==='tasks'){
  const requirement=(id:string)=>{const edge=model.relations.find(edge=>edge.dst===id)!;return `<div class="task-requirement" data-relation="${context.text(edge.id)}">${card(id)}</div>`;};
  markup=`<section class="task-board">${data.groups.map((group,index)=>`<section class="task-zone" data-surface="rectangle"><div class="task-scene">${context.glyph(data.icons[group.subjects[0]!]!)}</div>${heading(String.fromCharCode(65+index)+' · '+group.title,'heading')}<div class="task-parts" style="grid-template-columns:repeat(${group.columns},minmax(0,1fr))">${group.subjects.map(requirement).join('')}</div></section>`).join('')}</section><div class="task-join">${heading('ALL REQUIRED TOGETHER · ONE DECIDING VIEW','classification')}</div><section class="task-result" data-surface="rectangle"><div class="task-scene">${context.glyph(data.icons[data.activity!.entry!]!)}</div>${card(data.activity!.entry!)}</section>`;
 }else if(data.notation==='components'){
  const directed={...model,relations:model.relations.map(edge=>({...edge,srcArrow:'none' as const,dstArrow:'arrow' as const}))};
  const diagram=composeDiagram({...context,model:directed},modelDiagram(directed,{icons:data.icons,edgeLabels:false,options:{'elk.direction':'RIGHT','elk.algorithm':'layered','elk.spacing.nodeNode':'24','elk.layered.spacing.nodeNodeBetweenLayers':'32'}}));
  const guide=`<section class="architecture-guide">${data.groups.map(group=>`<section>${group.icon?`<div class="guide-icon">${context.glyph(group.icon)}</div>`:''}${lines(group.title,'heading',28)}</section>`).join('')}</section>`;
  return{markup:guide+diagram.markup,css:parts.map(part=>part.css).join('\n')+diagram.css+`.architecture-guide{display:grid;grid-template-columns:repeat(${data.groups.length},minmax(0,1fr));gap:20px;margin:18px 0}.architecture-guide>section{display:flex;align-items:center;gap:14px;background:var(--tint);padding:14px;border-radius:10px}.guide-icon{flex-shrink:0;color:var(--accent)}.guide-icon>svg{width:52px;height:52px}`};
 }else if(data.notation==='catalogue')markup=groups();
 else if(data.notation==='assurance')markup=groups(true);
 else if(data.notation==='dependencies'){
  const directed={...model,relations:model.relations.map(edge=>({...edge,srcArrow:'none' as const,dstArrow:'arrow' as const}))};
  return composeDiagram({...context,model:directed},modelDiagram(directed,{icons:data.icons,options:{'elk.direction':'RIGHT','elk.algorithm':'layered','elk.spacing.nodeNode':'30','elk.layered.spacing.nodeNodeBetweenLayers':'45'}}));
 }else if(data.notation==='bars'){
  const maximum=Math.max(1,...data.order.map(id=>data.metrics[id]!)),height=data.order.length*62+55;
  markup=`<div class="catalog-total">${heading(String(data.order.reduce((sum,id)=>sum+data.metrics[id]!,0))+' entries · '+data.order.length+' transport forms','heading')}</div><svg data-vector-surface xmlns="http://www.w3.org/2000/svg" role="img" aria-label="Native catalog entries by transport form" viewBox="0 0 1000 ${height}" width="100%" class="catalog-bars"><line x1="360" y1="12" x2="360" y2="${height-35}" stroke="var(--border)"/>${data.order.map((id,index)=>{const value=data.metrics[id]!,y=18+index*62;return `<g data-node="${context.text(id)}"><g transform="translate(0 ${y-8})">${data.icons[id]?context.glyph(data.icons[id]!).replace('<svg ', '<svg width="38" height="38" '):''}</g><text x="50" y="${y+18}" font-size="17" fill="var(--ink)">${context.text(title(id))}</text><rect x="360" y="${y}" width="${value/maximum*540}" height="28" rx="4" fill="var(--accent)"/><text x="930" y="${y+22}" font-size="19" fill="var(--ink)">${value}</text></g>`;}).join('')}<text x="360" y="${height-8}" font-size="14" fill="var(--muted)">0</text><text x="900" y="${height-8}" text-anchor="end" font-size="14" fill="var(--muted)">${maximum} entries</text></svg>`;
 }else throw new Error('Unknown declared notation');
 return{markup,css:[...new Set([...(illustrations?.values()??[])].map(part=>part.css))].join('\n')+parts.map(part=>part.css).join('\n')+`
.lane-critical{position:absolute;z-index:1;border:2px dashed var(--accent);border-radius:12px;background:transparent;pointer-events:none}.critical-label{position:absolute;right:12px;top:5px}.lane-headings{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:24px;margin:20px 0}.lane-heading{text-align:center}.lane-person{display:flex;justify-content:center;color:var(--accent);margin-bottom:8px}.lane-person>svg{width:54px;height:54px}.lane-canvas{position:relative;padding:14px 20px}.lane-backgrounds{position:absolute;inset:0;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:24px;z-index:0}.lane-backgrounds>div{background:var(--tint);border:1px solid var(--border);border-radius:12px}.lane-actions{position:relative;z-index:2;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));column-gap:64px;row-gap:18px;pointer-events:none}.lane-operation{align-self:center}.lane-operation .subject{padding:10px;border-color:var(--accent)}.lane-arrows{position:absolute;inset:0;width:100%;height:100%;z-index:1;overflow:visible}.lane-arrows path{stroke:var(--accent);stroke-width:2;fill:none}.task-board{display:grid;grid-template-columns:1fr 1.6fr 1fr;gap:20px;margin:20px 0 0}.task-zone{border:1px solid var(--border);background:var(--tint);border-radius:12px;padding:20px}.task-zone:nth-child(2){background:var(--surface)}.task-scene{display:flex;align-items:center;justify-content:center;color:var(--accent);height:70px;margin:0 0 8px}.task-scene>svg{width:64px;height:64px}.task-parts{display:grid;gap:12px;margin-top:18px}.task-parts .subject{padding:12px}.task-join{text-align:center;padding:18px 0}.task-result{display:flex;align-items:center;justify-content:center;gap:30px;border:2px solid var(--accent);border-radius:12px;background:var(--tint);padding:20px}.task-result .task-scene{height:auto;margin:0}.task-result .subject{position:relative;z-index:2;border:0;background:none}.reading-groups{display:grid;gap:22px;align-items:start}.reading-groups.components{grid-template-columns:repeat(2,minmax(0,1fr))}.reading-groups.catalogue{grid-template-columns:repeat(2,minmax(0,1fr))}.reading-groups.assurance{grid-template-columns:repeat(3,minmax(0,1fr))}.reading-group{position:relative;z-index:2;border:1px solid var(--border);background:var(--tint);border-radius:8px;padding:16px}.members{display:grid;gap:12px;margin-top:10px;align-items:start}.subject{position:relative;z-index:2;border:1px solid var(--border);background:var(--surface);border-radius:5px;padding:10px;min-width:0}.subject[data-proof-role="KernelLaw"]{border-color:var(--accent)}.subject[data-proof-role="KernelCounterexample"]{border-color:var(--secondary);background:var(--secondaryTint)}.subject[data-proof-role="HostPremise"]{border-color:var(--pending)}[data-heading-role="classification"] text{font-size:12px;fill:var(--muted);letter-spacing:.4px}.basis{margin-top:7px;padding-top:5px;border-top:1px solid var(--border)}.catalog-bars g>g>svg{width:38px;height:38px}.catalog-total{margin-top:16px}.group-heading{display:flex;align-items:center;gap:12px;min-height:54px}.group-scene{display:flex;flex-shrink:0;color:var(--accent)}.group-scene>svg{width:48px;height:48px}.catalog-bars{display:block;margin:24px 0;font-family:inherit}`};
}
