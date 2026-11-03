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
test('inventories refuse relationships; the responsibility matrix preserves direction and complete design coverage',()=>{
 expect(()=>bindNotation({notation:'catalogue',groups:[{title:'Both',subjects:['left','right']}]},mapping,model,{})).toThrow('discard');
 const rendered=html(bindNotation({notation:'matrix'},mapping,model,{}));
 expect(rendered).toContain('<table class="responsibilities">');
 expect(rendered).toContain('data-relation="native-link" data-from="native-left" data-to="native-right"');
 expect(rendered).not.toContain('data-from="native-right" data-to="native-left"');
});
test('assurance distinguishes checked lemma dependencies from explanatory links using the captured proof map',()=>{
 const actual=bindNotation({...grouped,proofDependencies:['invented']},mapping,model,{},proofs);
 expect(actual.proofDependencies).toEqual(['native-link']);
 expect(html(actual)).toContain('CHECKED LEMMA DEPENDENCY');
 const explanatory=bindNotation(grouped,mapping,model,{}, {...proofs,uses:[]});
 expect(html(explanatory)).toContain('READING RELATION');
 expect(html(explanatory)).not.toContain('CHECKED LEMMA DEPENDENCY');
 expect(()=>bindNotation(grouped,mapping,model,{})).toThrow('proof map');
});
test('quantity views require complete nonnegative SDK observations rather than caption-derived numbers',()=>{
 const inventory={...model,relations:[]};
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2})).toThrow('Missing');
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:-1,right:3})).toThrow('Invalid');
 expect(()=>bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2,right:3,invented:4})).toThrow('Invalid');
 expect(bindNotation({notation:'bars'},mapping,inventory,{},undefined,{left:2,right:0}).metrics).toEqual({'native-left':2,'native-right':0});
});
