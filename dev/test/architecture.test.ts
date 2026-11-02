// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {test,expect} from 'bun:test';
import {readFile,readdir} from 'node:fs/promises';
import {compileModel,readD2Figure} from '@deterministic-engineering/render';
import * as v from 'valibot';
import {ProjectionSchema} from '../projection';
const root=new URL('../../',import.meta.url);
async function declaration(name:string){
 const file=`dev/d2/${name}.d2`,raw=await readFile(new URL(file,root),'utf8');
 const compiled=await compileModel({[file]:raw},file);
 return {author:readD2Figure(compiled,{[file]:raw}),projection:v.parse(ProjectionSchema,JSON.parse(v.parse(v.object({figure:v.string()}),compiled.data).figure)).sysml};
}
test('Zero Trust is a model Component; diagram scopes do not promote it to the object foundation',async()=>{
 const overview=await declaration('architecture-overview'),components=await declaration('model-components');
 const model=await readFile(new URL(components.projection.source,root),'utf8');
 expect(model).toContain('part zeroTrust : Component;');
 expect(model).toContain('part leanPoo : Foundation;');
 expect(components.projection.bindings.zeroTrust?.name).toBe('CedarArchitecture::zeroTrust');
 expect(overview.projection.bindings.zeroTrust?.name).toBe('CedarArchitecture::zeroTrust');
 expect(overview.author.model!.relations.some(edge=>edge.src==='model'&&edge.dst==='zeroTrust')).toBe(true);
 expect(overview.author.model!.relations.some(edge=>edge.src==='zeroTrust'&&edge.dst==='leanPoo')).toBe(false);
 const exports=await readFile(new URL('CedarPooSpec.lean',root),'utf8');
 expect(exports).toContain('import CedarPooSpec.ZeroTrust');
});
test('every implemented vertical and platform has its own source-bound subject',async()=>{
 const {author,projection}=await declaration('verticals-platforms');
 for(const scope of ['Vertical','Platform']){
  const dirs=(await readdir(new URL(`CedarPooSpec/${scope}/`,root),{withFileTypes:true})).filter(entry=>entry.isDirectory());
  for(const dir of dirs){
   const prefix=`CedarPooSpec/${scope}/${dir.name}/`;
   const references=Object.entries(author.references).filter(([,source])=>source.startsWith(prefix));
   expect(references.length).toBeGreaterThan(0);
   expect(references.some(([ref])=>Object.hasOwn(projection.bindings,ref.replace(/Source$/,'')))).toBe(true);
  }
 }
 expect(Object.values(author.references).some(source=>source.startsWith('Examples/'))).toBe(false);
});
