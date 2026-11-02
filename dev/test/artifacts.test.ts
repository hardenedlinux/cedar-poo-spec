// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {readFile,readdir} from 'node:fs/promises';
import {sha,rendererDependency} from '../sources';
import {verifyFigure} from '../artifacts';
const root=new URL('../../',import.meta.url);
interface Receipt {binaries:Record<string,string>;sources:Record<string,string>;receipt:{drawing:string;pngSHA256:string;htmlSHA256:string;svgSHA256:string[];readability:{minimumTextSize:number}};sdk:{modelHash:string;view:string;trace:{modelHash:string}};lean?:{path:string;sha256:string};renderer:{specifier:string;name:string;version:string};entry:string;}
for(const name of (await readdir(new URL('../d2/',import.meta.url))).filter(name=>name.endsWith('.d2')).map(name=>name.slice(0,-3)).sort())test(name+' output binds actual input bytes, SDK model and hand-drawn artifacts',async()=>{
 const base='dev/d2/'+name,receipt:Receipt=JSON.parse(await readFile(new URL(base+'.json',root),'utf8'));
 await verifyFigure(root.pathname,base+'.d2');
 expect(sha(await readFile(new URL(base+'.png',root)))).toBe(receipt.receipt.pngSHA256);expect(sha(await readFile(new URL(base+'.svg',root)))).toBe(receipt.receipt.svgSHA256[0]!);expect(sha(await readFile(new URL(base+'.html',root)))).toBe(receipt.receipt.htmlSHA256);
 expect(receipt.receipt.drawing.startsWith('roughjs@')).toBe(true);expect(receipt.receipt.readability.minimumTextSize).toBeGreaterThanOrEqual(12);expect(receipt.sdk.modelHash).toBe(receipt.sdk.trace.modelHash);
 if(receipt.lean)expect(receipt.lean.sha256).toBe(sha(await readFile(new URL(receipt.lean.path,root))));
 expect(receipt.renderer.specifier).toBe(rendererDependency(JSON.parse(await readFile(new URL('dev/package.json',root),'utf8'))));

});

// Exercise the actual SDK receipts and exports, not synthetic transport snapshots.
test('real SDK view, renderer and catalog metadata cannot be mixed into another figure',async()=>{
 const {mkdtemp,mkdir,writeFile,rm}=await import('node:fs/promises'),{tmpdir}=await import('node:os'),{join,dirname}=await import('node:path');
 const entry='dev/d2/zero-trust-model-proofs.d2',stem=entry.slice(0,-3);
 const text=await readFile(new URL(stem+'.json',root),'utf8');
 const original:{sources:Record<string,string>;sdk:unknown;renderer:{version:string};proofClaims:{modelHash:string};lean?:unknown;receipt:{svgSHA256:string[]}}=JSON.parse(text);
 const other:{sdk:unknown}=JSON.parse(await readFile(new URL('dev/d2/zero-trust-object-proofs.json',root),'utf8'));
 const catalog:{lean:unknown}=JSON.parse(await readFile(new URL('dev/d2/lean-catalog.json',root),'utf8'));
 const temporary=await mkdtemp(join(tmpdir(),'cedar-real-receipt-'));
 try{
  for(const path of Object.keys(original.sources)){const destination=join(temporary,path);await mkdir(dirname(destination),{recursive:true});await writeFile(destination,await readFile(new URL(path,root)));}
  const extensions=['png','html','svg',...original.receipt.svgSHA256.slice(1).map((_,index)=>'scene-'+(index+1)+'.svg')];
  for(const extension of extensions)await writeFile(join(temporary,stem+'.'+extension),await readFile(new URL(stem+'.'+extension,root)));
  const receiptPath=join(temporary,stem+'.json');await writeFile(receiptPath,text);await verifyFigure(temporary,entry);
  const mixedSDK=structuredClone(original);mixedSDK.sdk=other.sdk;await writeFile(receiptPath,JSON.stringify(mixedSDK));await expect(verifyFigure(temporary,entry)).rejects.toThrow('SDK receipt binding');
  const mixedRenderer=structuredClone(original);mixedRenderer.renderer.version='unrelated';await writeFile(receiptPath,JSON.stringify(mixedRenderer));await expect(verifyFigure(temporary,entry)).rejects.toThrow('Renderer metadata binding');
  const mixedProof=structuredClone(original);mixedProof.proofClaims.modelHash=sha('another model');await writeFile(receiptPath,JSON.stringify(mixedProof));await expect(verifyFigure(temporary,entry)).rejects.toThrow('another model');
  const mixedCatalog=structuredClone(original);mixedCatalog.lean=catalog.lean;await writeFile(receiptPath,JSON.stringify(mixedCatalog));await expect(verifyFigure(temporary,entry)).rejects.toThrow('not captured');
 }finally{await rm(temporary,{recursive:true,force:true});}
},30000);
