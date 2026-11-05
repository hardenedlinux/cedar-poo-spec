// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {mkdtemp,mkdir,writeFile,rm} from 'node:fs/promises';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {figureSource,hostSources} from '../inputs';
import {assertCurrent,sha} from '../sources';
const entry='dev/d2/main.d2',helper='dev/d2/fragments/shared.d2',unrelated='dev/d2/unrelated.d2';
function declaration(references:Record<string,string>,body:string){
 const data={purpose:'architecture',language:'en',width:1120,primary:'scope',themes:['sketchbook'],icons:['engineering'],basis:{captureRef:'test-source',modelRefs:[],obligationRefs:[],evidenceRefs:[]},title:'Input closure',kind:'responsibility-map',questions:[{ref:'scope',text:'Which sources contribute?',focusRefs:['source']}],references:{source:entry,...references},copy:{description:'Native D2 source closure',status:'Filesystem control'}};
 return 'vars: {d2-config: {data: {figure: |json\n'+JSON.stringify(data)+'\n|\n}}}\n'+body;
}
async function fixture(files:Record<string,string>,run:(root:string)=>Promise<void>){
 const root=await mkdtemp(join(tmpdir(),'cedar-input-closure-'));
 try{for(const[path,bytes]of Object.entries(files)){await mkdir(join(root,path,'..'),{recursive:true});await writeFile(join(root,path),bytes);}await run(root);}
 finally{await rm(root,{recursive:true,force:true});}
}
test('native D2 closure excludes unrelated inputs and retains declared imports',async()=>{
 const files={[entry]:declaration({helper},'...@fragments/shared\na -> b'),[helper]:'a: A',[unrelated]:'unused: Before'};
 await fixture(files,async root=>{
  const first=await figureSource(root,files,entry);expect(Object.keys(first.author.sources).sort()).toEqual([entry,helper].sort());
  const hashes=Object.fromEntries(Object.entries(first.author.sources).map(([path,bytes])=>[path,sha(bytes)]));
  files[unrelated]='invalid unrelated syntax: {{{';await writeFile(join(root,unrelated),files[unrelated]);
  const next=await figureSource(root,files,entry);expect(next.author.sources).toEqual(first.author.sources);expect(next.author.model).toEqual(first.author.model);await assertCurrent(root,hashes);
  await writeFile(join(root,helper),'a: Changed');await expect(assertCurrent(root,hashes)).rejects.toThrow('changed');
 });
},30000);
test('the official D2 compiler rejects imports omitted from existing references',async()=>{
 const files={[entry]:declaration({},'...@fragments/shared\na -> b'),[helper]:'a: A'};
 await fixture(files,async root=>{await expect(figureSource(root,files,entry)).rejects.toThrow();});
},30000);
test('transitive imports must close through declared references as well',async()=>{
 const leaf='dev/d2/fragments/leaf.d2',files={[entry]:declaration({helper},'...@fragments/shared\na -> b'),[helper]:'...@leaf',[leaf]:'a: Leaf'};
 await fixture(files,async root=>{
  await expect(figureSource(root,files,entry)).rejects.toThrow();
  files[entry]=declaration({helper,leaf},'...@fragments/shared\na -> b');await writeFile(join(root,entry),files[entry]);
  expect(Object.keys((await figureSource(root,files,entry)).author.sources).sort()).toEqual([entry,helper,leaf].sort());
 });
},30000);
test('Bun observes imported host modules without invalidating for unused TS files',async()=>{
 await fixture({'dev/main.ts':'import {value} from "./used"; export const result=value;','dev/used.ts':'export const value=1;','dev/unused.ts':'export const ignored=1;'},async root=>{
  expect(await hostSources(root,'dev/main.ts')).toEqual(['dev/main.ts','dev/used.ts']);
  await writeFile(join(root,'dev/unused.ts'),'not even valid TypeScript!');
  expect(await hostSources(root,'dev/main.ts')).toEqual(['dev/main.ts','dev/used.ts']);
 });
});
