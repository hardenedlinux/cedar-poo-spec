// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import type {Model,SysMLValue} from '@openmbee/opensysml';
import * as v from 'valibot';
export const ProofViewSchema=v.object({proofs:v.optional(v.strictObject({namespace:v.pipe(v.string(),v.minLength(1))}))});
const Role=v.picklist(['Definition','KernelLaw','KernelCounterexample','HostPremise']);
export interface ProofCard {readonly id:string;readonly role:v.InferOutput<typeof Role>;readonly symbol:string;readonly source:string;}
export interface ProofMap {readonly modelHash:string;readonly cards:readonly ProofCard[];readonly uses:readonly {dependency:string;target:string}[];}
const identifier=(name:string)=>name.length>0&&[...name].every((c,i)=>c==='_'||c>='A'&&c<='Z'||c>='a'&&c<='z'||i>0&&c>='0'&&c<='9');
const theorem=(card:ProofCard)=>card.role==='KernelLaw'||card.role==='KernelCounterexample';
function string(value:SysMLValue):string{
 if(value.kind!=='string'||!value.value.trim())throw new Error('Proof metadata must be a nonempty SDK string');
 return value.value;
}
/** Read the parsed model only. SysML syntax, names, types and values belong to the SDK. */
export async function readProofMap(model:Model,namespace:string):Promise<ProofMap>{
 const children=await (await model.symbol(namespace)).children(),parts=children.filter(symbol=>symbol.kind==='partUsage');
 if(!parts.length)throw new Error('Empty proof declaration scope');
 const cards:ProofCard[]=[];
 for(const part of parts){
  const role=v.parse(Role,part.type?.resolvedId.slice(namespace.length+2));
  if(part.type?.resolvedId!==namespace+'::'+role)throw new Error('Proof role is outside the selected namespace');
  const symbol=string(await model.eval(part.id+'Symbol')),source=string(await model.eval(part.id+'Source'));
  if(!symbol.split('.').every(identifier))throw new Error('Invalid Lean declaration name');
  if(!source.endsWith('.lean')||!source.slice(0,-5).split('/').every(identifier))throw new Error('Invalid Lean source module');
  cards.push({id:part.id,role,symbol,source});
 }
 const ids=new Set(cards.map(card=>card.id));
 for(const attribute of children.filter(symbol=>symbol.kind==='attributeUsage'&&symbol.name.endsWith('Uses')))if(!ids.has(attribute.id.slice(0,-4)))throw new Error('Unbound proof-use owner');
 const byId=new Map(cards.map(card=>[card.id,card])),uses:ProofMap['uses'][number][]=[],edges=new Set<string>();
 for(const view of children.filter(symbol=>symbol.kind==='viewUsage')){
  const rendering=await model.connection.renderView(model.hash,view.id,{depth:1});
  const nodes=new Map(rendering.nodes.map(node=>[node.id,node.name]));
  for(const edge of rendering.edges)edges.add(JSON.stringify([nodes.get(edge.from),nodes.get(edge.to)]));
 }
 for(const target of cards){
  const attribute=children.find(symbol=>symbol.id===target.id+'Uses');
  if(!attribute)continue;
  if(!theorem(target))throw new Error('Only a theorem may claim proof-term uses');
  const value=await model.eval(attribute.id),values=value.kind==='sequence'?value.elements:[value];
  const seen=new Set<string>();
  for(const value of values){
   const referenced=await model.symbol(string(value)),dependency=byId.get(referenced.id);
   if(!dependency||!theorem(dependency))throw new Error('Proof use must bind a declared theorem');
   if(seen.has(dependency.id))throw new Error('Duplicate proof-use claim');seen.add(dependency.id);
   if(!edges.has(JSON.stringify([dependency.id,target.id])))throw new Error('Proof-use claim has no SDK view edge');
   uses.push({dependency:dependency.symbol,target:target.symbol});
  }
 }
 return{modelHash:model.hash,cards,uses};
}
/** Native Lean owns declaration kinds, defining modules and proof-term inspection. */
export function leanProofCheck(map:ProofMap):string{
 const name=(value:string)=>'`'+value;
 const origins=map.cards.map(card=>[card.symbol,card.source.slice(0,-5).split('/').join('.')] as const);
 return `import Lean.Elab.BuiltinEvalCommand
import Lean.Util.FoldConsts
${[...new Set(origins.map(([,module])=>module))].sort().map(module=>'import '+module).join('\n')}
run_cmd do
  let env ← Lean.getEnv
  for (name, moduleName) in [${origins.map(([symbol,module])=>'('+name(symbol)+', '+name(module)+')').join(', ')}] do
    unless (env.find? name).isSome do throwError "missing diagram declaration: {name}"
    let some actual ← pure (env.getModuleIdxFor? name) | throwError "missing declaration origin: {name}"
    let some expected ← pure (env.getModuleIdx? moduleName) | throwError "missing source module: {moduleName}"
    unless actual == expected do throwError "diagram declaration/source mismatch: {name}"
  for name in ([${map.cards.filter(theorem).map(card=>name(card.symbol)).join(', ')}] : List Lean.Name) do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "diagram law is not a theorem: {name}"
  for (dependency, name) in ([${map.uses.map(use=>'('+name(use.dependency)+', '+name(use.target)+')').join(', ')}] : List (Lean.Name × Lean.Name)) do
    match env.find? name with
    | some (.thmInfo info) =>
      unless info.value.getUsedConstants.contains dependency do
        throwError "diagram lemma edge absent from proof term: {dependency} -> {name}"
    | _ => throwError "diagram target is not a theorem: {name}"
  Lean.logInfo "PROOF-FIGURES-LEAN-OK"
`;
}
