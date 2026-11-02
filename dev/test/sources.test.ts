// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {mkdtemp,mkdir,writeFile,unlink,rm,symlink} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {assertCurrent,captureFiles,repositoryPath,rendererDependency,sha} from '../sources';

test('changed/missing model, D2, JSON, adapter, package inputs and executable invalidate publication',async()=>{
 const root=await mkdtemp(join(tmpdir(),'cedar-view-sources-'));
 try{
  for(const file of ['model.sysml','view.d2','catalog.json','adapter.ts','package.json','bun.lock','producer']){
   await writeFile(join(root,file),'captured bytes');
   const hashes={[file]:sha('captured bytes')};await assertCurrent(root,hashes);
   await writeFile(join(root,file),'different bytes');
   await expect(assertCurrent(root,hashes)).rejects.toThrow('changed');
   await writeFile(join(root,file),'captured bytes');
   await assertCurrent(root,hashes); // Content identity, not mtime/cache identity.
   await unlink(join(root,file));await expect(assertCurrent(root,hashes)).rejects.toThrow();
  }
 }finally{await rm(root,{recursive:true,force:true});}
});
test('source declarations cannot escape the repository through paths or symlinks',async()=>{
 const base=await mkdtemp(join(tmpdir(),'cedar-view-boundary-')),root=join(base,'repo');
 try{
  await mkdir(root);await writeFile(join(base,'outside'),'secret');await symlink(join(base,'outside'),join(root,'alias'));
  await expect(repositoryPath(root,'../outside')).rejects.toThrow('escapes');
  await expect(captureFiles(root,['alias'])).rejects.toThrow('escapes');
  await writeFile(join(root,'inside'),'source');expect(await captureFiles(root,['inside'])).toEqual({inside:'source'});
 }finally{await rm(base,{recursive:true,force:true});}
});

test('renderer dependency follows package.json; Bun owns specifier resolution',()=>{
 const manifest=(spec:unknown)=>({dependencies:{'@deterministic-engineering/render':spec}});
 for(const spec of ['git+https://github.com/example/render.git#reviewed','github:example/render#reviewed','1.0.1'])expect(rendererDependency(manifest(spec))).toBe(spec);
 for(const spec of [undefined,42,''])expect(()=>rendererDependency(manifest(spec))).toThrow();
 expect(()=>rendererDependency({})).toThrow();
});
