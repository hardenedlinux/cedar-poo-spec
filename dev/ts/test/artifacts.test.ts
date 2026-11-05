// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {readFile,readdir} from 'node:fs/promises';
import {sha,rendererDependency} from '../sources';
import {verifyFigure,htmlArtifact,receiptArtifact} from '../artifacts';
import {figureSource} from '../inputs';
const root=new URL('../../../',import.meta.url);
interface Receipt {binaries:Record<string,string>;sources:Record<string,string>;receipt:{drawing:string;pngSHA256:string;htmlSHA256:string;svgSHA256:string[];readability:{minimumTextSize:number}};sdk:{modelHash:string;view:string;trace:{modelHash:string}};lean?:{path:string;sha256:string};renderer:{specifier:string;name:string;version:string};entry:string;}
for(const name of (await readdir(new URL('../../d2/',import.meta.url))).filter(name=>name.endsWith('.d2')).map(name=>name.slice(0,-3)).sort())test(name+' output binds actual input bytes, SDK model and source-selected vector artifacts',async()=>{
 const base='dev/d2/'+name,receipt:Receipt=JSON.parse(await readFile(new URL(receiptArtifact(base+'.d2'),root),'utf8'));
 await verifyFigure(root.pathname,base+'.d2');
 expect(await Bun.file(new URL(base+'.json',root)).exists()).toBe(false);
 expect(await Bun.file(new URL(base+'.html',root)).exists()).toBe(false);
 expect(sha(await readFile(new URL(base+'.png',root)))).toBe(receipt.receipt.pngSHA256);expect(sha(await readFile(new URL(base+'.svg',root)))).toBe(receipt.receipt.svgSHA256[0]!);expect(sha(await readFile(new URL(htmlArtifact(base+'.d2'),root)))).toBe(receipt.receipt.htmlSHA256);
 const declaredSources=Object.fromEntries(await Promise.all(Object.keys(receipt.sources).filter(path=>path.endsWith('.d2')).map(async path=>[path,await readFile(new URL(path,root),'utf8')])));
 const {author}=await figureSource(root.pathname,declaredSources,receipt.entry);
 if(author.theme?.drawing.mode==='sketch')expect(receipt.receipt.drawing.startsWith('roughjs@')).toBe(true);
 else expect(receipt.receipt.drawing).toBe('precise');expect(receipt.receipt.readability.minimumTextSize).toBeGreaterThanOrEqual(12);expect(receipt.sdk.modelHash).toBe(receipt.sdk.trace.modelHash);
 if(receipt.lean)expect(receipt.lean.sha256).toBe(sha(await readFile(new URL(receipt.lean.path,root))));
 expect(receipt.renderer.specifier).toBe(rendererDependency(JSON.parse(await readFile(new URL('dev/package.json',root),'utf8'))));

});

// Exercise the actual SDK receipts and exports, not synthetic transport snapshots.
test('real SDK view, renderer and catalog metadata cannot be mixed into another figure',async()=>{
 const {mkdtemp,mkdir,writeFile,rm}=await import('node:fs/promises'),{tmpdir}=await import('node:os'),{join,dirname}=await import('node:path');
 const entry='dev/d2/zero-trust-model-proofs.d2',stem=entry.slice(0,-3);
 const text=await readFile(new URL(receiptArtifact(entry),root),'utf8');
 const original:{sources:Record<string,string>;sdk:unknown;renderer:{version:string};proofClaims:{modelHash:string};lean?:unknown;receipt:{svgSHA256:string[]}}=JSON.parse(text);
 const other:{sdk:unknown}=JSON.parse(await readFile(new URL(receiptArtifact('dev/d2/zero-trust-object-proofs.d2'),root),'utf8'));
 const catalog:{lean:unknown}=JSON.parse(await readFile(new URL(receiptArtifact('dev/d2/lean-catalog.d2'),root),'utf8'));
 const temporary=await mkdtemp(join(tmpdir(),'cedar-real-receipt-'));
 try{
  for(const path of Object.keys(original.sources)){const destination=join(temporary,path);await mkdir(dirname(destination),{recursive:true});await writeFile(destination,await readFile(new URL(path,root)));}
  const extensions=['png','html','svg',...original.receipt.svgSHA256.slice(1).map((_,index)=>'scene-'+(index+1)+'.svg')];
  for(const extension of extensions){const path=extension==='html'?htmlArtifact(entry):stem+'.'+extension;await mkdir(dirname(join(temporary,path)),{recursive:true});await writeFile(join(temporary,path),await readFile(new URL(path,root)));}
  const receiptPath=join(temporary,receiptArtifact(entry));await writeFile(receiptPath,text);await verifyFigure(temporary,entry);
  const mixedSDK=structuredClone(original);mixedSDK.sdk=other.sdk;await writeFile(receiptPath,JSON.stringify(mixedSDK));await expect(verifyFigure(temporary,entry)).rejects.toThrow('SDK receipt binding');
  const mixedRenderer=structuredClone(original);mixedRenderer.renderer.version='unrelated';await writeFile(receiptPath,JSON.stringify(mixedRenderer));await expect(verifyFigure(temporary,entry)).rejects.toThrow('Renderer metadata binding');
  const mixedProof=structuredClone(original);mixedProof.proofClaims.modelHash=sha('another model');await writeFile(receiptPath,JSON.stringify(mixedProof));await expect(verifyFigure(temporary,entry)).rejects.toThrow('another model');
  const mixedCatalog=structuredClone(original);mixedCatalog.lean=catalog.lean;await writeFile(receiptPath,JSON.stringify(mixedCatalog));await expect(verifyFigure(temporary,entry)).rejects.toThrow('not captured');
 }finally{await rm(temporary,{recursive:true,force:true});}
},30000);

// Restore actual SDK/browser outputs into a different root; never reissue a receipt.
test('restored real exports require their cache and exact captured sources',async()=>{
 const {mkdtemp,mkdir,writeFile,rm,unlink,lstat}=await import('node:fs/promises');
 const {tmpdir}=await import('node:os'),{join,dirname}=await import('node:path');
 const entry='dev/d2/architecture-overview.d2',stem=entry.slice(0,-3);
 const receipt:Receipt=JSON.parse(await readFile(new URL(receiptArtifact(entry),root),'utf8'));
 const temporary=await mkdtemp(join(tmpdir(),'cedar-restored-view-'));
 const copy=async(path:string)=>{await mkdir(dirname(join(temporary,path)),{recursive:true});await writeFile(join(temporary,path),await readFile(new URL(path,root)));};
 try{
  // This non-catalog view must restore without any native producer or vendor tree.
  expect(receipt.binaries).toEqual({});
  for(const path of Object.keys(receipt.sources))await copy(path);
  for(const path of [receiptArtifact(entry),stem+'.png',stem+'.svg',...receipt.receipt.svgSHA256.slice(1).map((_,index)=>stem+'.scene-'+(index+1)+'.svg')])await copy(path);
  await expect(verifyFigure(temporary,entry)).rejects.toThrow(); // HTML not restored yet.
  await copy(htmlArtifact(entry));await verifyFigure(temporary,entry);
  const mutations=[entry,'Project.sysml',...Object.keys(receipt.sources).filter(path=>path.endsWith('.sysml')),'dev/ts/render.ts','dev/package.json','dev/bun.lock'];
  expect(mutations.some(path=>path.endsWith('.sysml'))).toBe(true);
  for(const path of mutations){
   expect(Object.hasOwn(receipt.sources,path)).toBe(true);
   const original=await readFile(new URL(path,root),'utf8');
   if(path==='dev/package.json'){const manifest=JSON.parse(original);delete manifest.dependencies.parse5;await writeFile(join(temporary,path),JSON.stringify(manifest));}
   else await writeFile(join(temporary,path),original+'\n');
   await expect(verifyFigure(temporary,entry)).rejects.toThrow('changed');
   await copy(path);await verifyFigure(temporary,entry);
  }
  await unlink(join(temporary,htmlArtifact(entry)));
  await expect(verifyFigure(temporary,entry)).rejects.toThrow();
  await copy(htmlArtifact(entry));await verifyFigure(temporary,entry);
  expect(await Bun.file(join(temporary,stem+'.html')).exists()).toBe(false);
  await expect(lstat(join(temporary,'dev/vendor'))).rejects.toMatchObject({code:'ENOENT'});
 }finally{await rm(temporary,{recursive:true,force:true});}
},30000);
