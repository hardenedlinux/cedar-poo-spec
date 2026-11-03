// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {test,expect} from 'bun:test';
import {composeFigure,composeHeading,defineDesign,type FigureModel} from '@deterministic-engineering/render';
import {bindNotation,composeNotation} from '../notation';
import type {ProofMap} from '../proofs';
const model:FigureModel={subjects:[{id:'native-left',type:'partUsage',sourceName:'Fixture::left',label:'Left capability'},{id:'native-right',type:'partUsage',sourceName:'Fixture::right',label:'Right capability'}],relations:[{id:'native-link',src:'native-left',dst:'native-right',label:'Original requirement'}]};
const mapping={left:'native-left',right:'native-right'};
const grouped={notation:'assurance',groups:[{title:'Argument',subjects:['left','right']}]};
const proofs:ProofMap={modelHash:'fixture',cards:[{id:'Fixture::left',role:'KernelLaw',symbol:'Fixture.left',source:'Fixture.lean'},{id:'Fixture::right',role:'KernelLaw',symbol:'Fixture.right',source:'Fixture.lean'}],uses:[{dependency:'Fixture.left',target:'Fixture.right'}]};
function html(presentation:ReturnType<typeof bindNotation>){
 const question={ref:'purpose',text:'Which declared relationship is retained?',focusRefs:['source']};
 return composeFigure({width:1200,language:'en',sources:{'fixture.txt':'actual test fixture','fixture.d2':'captured notation fixture'},references:{source:'fixture.txt'},questions:[question],view:{source:'fixture.d2',title:'Fixture',purpose:'architecture',kind:'responsibility-map',question,basis:{captureRef:'fixture',modelRefs:[],obligationRefs:[],evidenceRefs:[]}},model,presentation,design:defineDesign({audience:'test',medium:'repository',message:'retain source relations',questionRefs:['purpose'],requiredSubjects:model.subjects.map(node=>node.id),requiredRelations:model.relations.map(edge=>edge.id),focalSubjects:[]})},context=>{
  const heading=composeHeading(context,{text:question.text,role:'question',questionRef:'purpose'}),body=composeNotation(context);
  return{markup:heading.markup+body.markup,css:heading.css+body.css};
 }).html;
}
test('reading groups cannot invent, duplicate or omit captured subjects',()=>{
 expect(()=>bindNotation({notation:'components',groups:[{title:'Only one',subjects:['left']}]},mapping,model,{})).toThrow('exactly one');
 expect(()=>bindNotation({notation:'components',groups:[{title:'Duplicate',subjects:['left','left']}]},mapping,model,{})).toThrow('exactly one');
 expect(()=>bindNotation({notation:'components',groups:[{title:'Invented',subjects:['left','missing']}]},mapping,model,{})).toThrow('Unknown');
});
test('inventories refuse relationships; the responsibility view preserves direction and complete design coverage',()=>{
 expect(()=>bindNotation({notation:'catalogue',groups:[{title:'Both',subjects:['left','right']}]},mapping,model,{})).toThrow('discard');
 const rendered=html(bindNotation({notation:'dependencies'},mapping,model,{}));
 expect(rendered).toContain('data-scene-edge');
 expect(rendered).not.toContain('<table');
 expect(rendered).toContain('data-scene-edge="native-link"');
 expect(rendered).toContain('data-source-id="native-left" data-target-id="native-right"');
 expect(rendered).not.toContain('data-source-id="native-right" data-target-id="native-left"');
});
test('assurance distinguishes checked lemma dependencies from explanatory links using the captured proof map',()=>{
 const actual=bindNotation({...grouped,proofDependencies:['invented']},mapping,model,{},proofs);
 expect(actual.proofDependencies).toEqual(['native-link']);
 expect(html(actual)).toContain('PROOF A1 → A2');
 const explanatory=bindNotation(grouped,mapping,model,{}, {...proofs,uses:[]});
 expect(html(explanatory)).toContain('CONTEXT A1 → A2');
 expect(html(explanatory)).not.toContain('PROOF A1 → A2');
 expect(()=>bindNotation(grouped,mapping,model,{})).toThrow('proof map');
});
test('quantity views require complete nonnegative SDK observations rather than caption-derived numbers',()=>{
 const inventory={...model,relations:[]};
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2})).toThrow('Missing');
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:-1,right:3})).toThrow('Invalid');
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2,right:3,invented:4})).toThrow('Invalid');
 expect(bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2,right:0}).metrics).toEqual({'native-left':2,'native-right':0});
});

const activityModel:FigureModel={subjects:[...model.subjects,{id:'native-end',type:'partUsage',sourceName:'Fixture::end',label:'Refused'}],relations:[{id:'yes',src:'native-left',dst:'native-right',label:'ok'},{id:'no',src:'native-left',dst:'native-end',label:'error'}]};
const activityMapping={...mapping,end:'native-end'};
const activityProofs:ProofMap={...proofs,cards:[...proofs.cards,{id:'Fixture::end',role:'Definition',symbol:'Fixture.end',source:'Fixture.lean'}]};
test('workflow semantics refuse cycles, unreachable work, unfinished outcomes and unlabelled alternatives',()=>{
 const declared={notation:'workflow',activity:{entry:'left',decisions:['left'],terminals:['right','end']}};
 expect(bindNotation(declared,activityMapping,activityModel,{},activityProofs).activity?.terminals).toEqual(['native-right','native-end']);
 expect(()=>bindNotation(declared,activityMapping,{...activityModel,relations:[activityModel.relations[0]!]},{},activityProofs)).toThrow('Unreachable');
 expect(()=>bindNotation(declared,activityMapping,{...activityModel,relations:activityModel.relations.map(edge=>({...edge,label:''}))},{},activityProofs)).toThrow('labelled');
 expect(()=>bindNotation({...declared,activity:{...declared.activity,terminals:['right']}},activityMapping,activityModel,{},activityProofs)).toThrow('successor');
 expect(()=>bindNotation(declared,activityMapping,{...activityModel,relations:[...activityModel.relations,{id:'cycle',src:'native-right',dst:'native-left',label:'repeat'}]},{},activityProofs)).toThrow();
 expect(()=>bindNotation(declared,activityMapping,activityModel,{})).toThrow('captured Lean');
});
test('swimlanes need one owner and one ordered stage for every operation; backwards handoffs refuse',()=>{
 const declared={notation:'swimlanes',groups:[{title:'Caller',subjects:['left']},{title:'Authority',subjects:['right']}],activity:{stages:[{title:'Prepare',subjects:['left']},{title:'Commit',subjects:['right']}]}};
 expect(bindNotation(declared,mapping,model,{}).activity?.stages).toHaveLength(2);
 expect(()=>bindNotation({...declared,groups:[{title:'Both',subjects:['left','left']}]},mapping,model,{})).toThrow('exactly one');
 expect(()=>bindNotation({...declared,activity:{stages:[{title:'Only',subjects:['left']}]}},mapping,model,{})).toThrow('one stage');
 expect(()=>bindNotation({...declared,activity:{stages:[...declared.activity.stages].reverse()}},mapping,model,{})).toThrow('advance');
 expect(()=>bindNotation({...declared,activity:{stages:declared.activity.stages,terminals:['right']}},mapping,model,{})).toThrow('stages');
});
test('task requirements are a rooted AND tree, not branching outcomes or completion claims',()=>{
 const requirements={...model,relations:model.relations.map(edge=>({...edge,label:'requires'}))};
 expect(bindNotation({notation:'tasks',groups:[{title:'Required',subjects:['right']}],activity:{entry:'left'}},mapping,requirements,{},proofs).notation).toBe('tasks');
 expect(()=>bindNotation({notation:'tasks',groups:[{title:'Required',subjects:['right']}],activity:{entry:'left'}},mapping,model,{},proofs)).toThrow('requires');
 expect(()=>bindNotation({notation:'tasks',groups:[{title:'Required',subjects:['right']}],activity:{entry:'left',terminals:['right']}},mapping,requirements,{},proofs)).toThrow('conjunctive');
 expect(()=>bindNotation({notation:'catalogue',groups:[{title:'All',subjects:['left','right']}],activity:{entry:'left'}},mapping,{...model,relations:[]},{})).toThrow('Static');
});

test('swimlane critical scope cannot silently skip an intervening stage',()=>{
 const linear={...activityModel,relations:[{id:'a',src:'native-left',dst:'native-right',label:'next'},{id:'b',src:'native-right',dst:'native-end',label:'next'}]};
 const activity={stages:[{title:'Check',subjects:['left']},{title:'Install',subjects:['right']},{title:'Observe',subjects:['end']}],critical:{title:'Lock',subjects:['left','right','end']}};
 expect(bindNotation({notation:'swimlanes',groups:[{title:'Authority',subjects:['left','right','end']}],activity},activityMapping,linear,{}).activity?.critical?.subjects).toHaveLength(3);
 expect(()=>bindNotation({notation:'swimlanes',groups:[{title:'Authority',subjects:['left','right','end']}],activity:{...activity,critical:{title:'Lock',subjects:['left','end']}}},activityMapping,linear,{})).toThrow('contiguous');
});
