// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {readFile,writeFile,rename,unlink,mkdtemp,rm,readdir,mkdir} from 'node:fs/promises';
import {resolve,dirname,join,basename} from 'node:path';
import {isDeepStrictEqual} from 'node:util';
import {parse,type DefaultTreeAdapterMap} from 'parse5';
import * as v from 'valibot';
import type {FigureImage} from '@deterministic-engineering/render/export';
import {assertCurrent,repositoryPath,sha} from './sources';

const hash=v.pipe(v.string(),v.check(value=>value.length===64&&[...value].every(c=>'0123456789abcdef'.includes(c))));
const hashes=v.record(v.string(),hash);
const Receipt=v.object({entry:v.string(),sources:hashes,binaries:hashes,receipt:v.object({inputSHA256:hash,htmlSHA256:hash,pngSHA256:hash,svgSHA256:v.pipe(v.array(hash),v.minLength(1))}),sdk:v.optional(v.object({modelHash:hash,view:v.string(),trace:v.unknown()})),renderer:v.optional(v.object({name:v.string(),version:v.string()})),lean:v.optional(v.object({path:v.string(),sha256:hash})),proofClaims:v.optional(v.object({modelHash:hash}))});
const Provenance=v.object({inputSHA256:hash,sourceSHA256:hashes,view:v.object({source:v.string()}),modelSource:v.optional(v.object({modelHash:hash,view:v.string()})),modelTrace:v.optional(v.unknown()),renderer:v.optional(v.object({package:v.string(),version:v.string()}))});
export interface PublicationInputs {readonly entry:string;readonly sources:Readonly<Record<string,string>>;readonly binaries:Readonly<Record<string,string>>;}
export type ExportedFiles=Pick<FigureImage,'png'|'svg'|'html'> & {readonly receipt:Pick<FigureImage['receipt'],'inputSHA256'|'htmlSHA256'|'pngSHA256'|'svgSHA256'>};
const svgName=(index:number)=>index===0?'svg':`scene-${index}.svg`;
export const htmlArtifact=(entry:string)=>'.cache/render/'+base(entry)+'.html';
function base(entry:string):string{
 if(!entry.endsWith('.d2'))throw new Error('Expected a D2 figure entry');
 return entry.slice(0,-3);
}
function checkHTML(html:string,receipt:v.InferOutput<typeof Receipt>){
 const queue:DefaultTreeAdapterMap['node'][]=[parse(html)],values:string[]=[];
 while(queue.length){
  const node=queue.pop()!;
  if('tagName'in node&&node.tagName==='script'&&node.attrs.some(attr=>attr.name==='id'&&attr.value==='figure-provenance')){
   if(!node.attrs.some(attr=>attr.name==='type'&&attr.value==='application/json'))throw new Error('Invalid figure provenance media type');
   values.push(node.childNodes.map(child=>'value'in child?child.value:'').join(''));
  }
  if('childNodes'in node)queue.push(...node.childNodes);
 }
 if(values.length!==1)throw new Error('Expected one native figure provenance record');
 const provenance=v.parse(Provenance,JSON.parse(values[0]!));
 if(provenance.view.source!==receipt.entry||provenance.inputSHA256!==receipt.receipt.inputSHA256||!isDeepStrictEqual(provenance.sourceSHA256,receipt.sources))throw new Error('HTML / receipt input binding mismatch');
 if(Boolean(provenance.modelSource)!==Boolean(receipt.sdk)||receipt.sdk&&(provenance.modelSource?.modelHash!==receipt.sdk.modelHash||provenance.modelSource?.view!==receipt.sdk.view||!isDeepStrictEqual(provenance.modelTrace,receipt.sdk.trace)))throw new Error('HTML / SDK receipt binding mismatch');
 if(receipt.renderer&&(provenance.renderer?.package!==receipt.renderer.name||provenance.renderer?.version!==receipt.renderer.version))throw new Error('Renderer metadata binding mismatch');
 if(receipt.lean&&receipt.sources[receipt.lean.path]!==receipt.lean.sha256)throw new Error('Catalog input is not captured by this figure');
 if(receipt.proofClaims?.modelHash!==undefined&&receipt.proofClaims.modelHash!==receipt.sdk?.modelHash)throw new Error('Proof claims belong to another model');
}
function checkFiles(image:ExportedFiles,receipt:v.InferOutput<typeof Receipt>){
 if(image.svg.length!==receipt.receipt.svgSHA256.length)throw new Error('SVG output set does not match the renderer receipt');
 if(sha(image.png)!==receipt.receipt.pngSHA256||sha(image.html)!==receipt.receipt.htmlSHA256||image.svg.some((svg,index)=>sha(svg)!==receipt.receipt.svgSHA256[index]))throw new Error('Figure artifact hash mismatch');
 checkHTML(image.html,receipt);
}
/** Verify current sources and the existing renderer receipt; no cached admission result. */
export async function verifyFigure(root:string,entry:string,expectedInputSHA256?:string){
 const stem=base(entry),receipt=v.parse(Receipt,JSON.parse(await readFile(await repositoryPath(root,stem+'.json'),'utf8')));
 if(receipt.entry!==entry||!Object.hasOwn(receipt.sources,entry))throw new Error('Receipt belongs to another figure entry');
 if(expectedInputSHA256!==undefined&&receipt.receipt.inputSHA256!==expectedInputSHA256)throw new Error('Unexpected figure input');
 await assertCurrent(root,{...receipt.sources,...receipt.binaries});
 const expected=new Set(receipt.receipt.svgSHA256.map((_,index)=>basename(stem)+'.'+svgName(index)));
 for(const file of await readdir(resolve(root,dirname(stem))))if(file.startsWith(basename(stem)+'.scene-')&&file.endsWith('.svg')&&!expected.has(file))throw new Error('Unlisted scene artifact');
 const png=await readFile(await repositoryPath(root,stem+'.png')),svg=await Promise.all(receipt.receipt.svgSHA256.map(async(_,index)=>readFile(await repositoryPath(root,stem+'.'+svgName(index)),'utf8'))),html=await readFile(await repositoryPath(root,htmlArtifact(entry)),'utf8');
 checkFiles({png,svg,html,receipt:receipt.receipt},receipt);
 return receipt;
}
/** Filesystem effect only. Invalidate first, stage bytes, then commit the native receipt last. */
export async function publishFigure<T extends PublicationInputs>(root:string,inputs:T,generate:()=>Promise<ExportedFiles>):Promise<void>{
 const stem=resolve(root,base(inputs.entry)),receiptPath=stem+'.json';
 await repositoryPath(root,inputs.entry);
 await unlink(receiptPath).catch((error:NodeJS.ErrnoException)=>{if(error.code!=='ENOENT')throw error;});
 await unlink(stem+'.html').catch((error:NodeJS.ErrnoException)=>{if(error.code!=='ENOENT')throw error;});
 let temporary:string|undefined;
 try{
  await assertCurrent(root,{...inputs.sources,...inputs.binaries});
  const image=await generate(),payload={...inputs,receipt:image.receipt},checked=v.parse(Receipt,payload);
  if(!Object.hasOwn(checked.sources,inputs.entry))throw new Error('Uncaptured figure entry');
  checkFiles(image,checked);
  temporary=await mkdtemp(join(dirname(stem),'.export-'));
  const files:[string,string|Uint8Array][]=[['png',image.png],...image.svg.map((svg,index):[string,string]=>[svgName(index),svg]),['html',image.html]];
  for(const[extension,bytes]of files)await writeFile(join(temporary,extension),bytes);
  await writeFile(join(temporary,'json'),JSON.stringify(payload,null,2)+'\n');
  await assertCurrent(root,{...inputs.sources,...inputs.binaries});
  for(const file of await readdir(dirname(stem),{withFileTypes:true}))if((file.isFile()||file.isSymbolicLink())&&file.name.startsWith(basename(stem)+'.scene-')&&file.name.endsWith('.svg'))await unlink(join(dirname(stem),file.name));
  const htmlPath=resolve(root,htmlArtifact(inputs.entry));await mkdir(dirname(htmlPath),{recursive:true});await repositoryPath(root,dirname(htmlPath));
  for(const[extension]of files)await rename(join(temporary,extension),extension==='html'?htmlPath:stem+'.'+extension);
  await assertCurrent(root,{...inputs.sources,...inputs.binaries});
  await rename(join(temporary,'json'),receiptPath);
  await verifyFigure(root,inputs.entry,image.receipt.inputSHA256);
 }catch(error){await unlink(receiptPath).catch((failure:NodeJS.ErrnoException)=>{if(failure.code!=='ENOENT')throw failure;});throw error;}
 finally{if(temporary)await rm(temporary,{recursive:true,force:true});}
}
