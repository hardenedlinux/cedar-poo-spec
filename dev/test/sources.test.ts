// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {mkdtemp,mkdir,writeFile,unlink,rm,symlink} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {assertCurrent,captureFiles,repositoryPath,rendererArchive,sha} from '../sources';

test('changed/missing model, D2, JSON, adapter, archive and executable invalidate publication',async()=>{
 const root=await mkdtemp(join(tmpdir(),'cedar-view-sources-'));
 try{
  for(const file of ['model.sysml','view.d2','catalog.json','adapter.ts','renderer.tgz','producer']){
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

test('renderer archive follows the existing package declaration, with no second revision pin',()=>{
 const manifest=(spec:unknown)=>({dependencies:{'@deterministic-engineering/render':spec}});
 expect(rendererArchive(manifest('file:vendor/new-revision.tgz'))).toBe('dev/vendor/new-revision.tgz');
 for(const spec of [undefined,42,'file:../outside.tgz','file:/outside.tgz','file:vendor/../../outside.tgz','https://example.org/package.tgz'])expect(()=>rendererArchive(manifest(spec))).toThrow();
 expect(()=>rendererArchive({})).toThrow();
});
