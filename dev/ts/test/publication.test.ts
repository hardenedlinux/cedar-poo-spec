// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {mkdtemp,mkdir,writeFile,readFile,unlink,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {publishFigure,verifyFigure,htmlArtifact,receiptArtifact,type ExportedFiles} from '../artifacts';
import {sha} from '../sources';
const entry='dev/d2/case.d2',stem=entry.slice(0,-3);
const output=(extension:string)=>extension==='html'?htmlArtifact(entry):extension==='json'?receiptArtifact(entry):stem+'.'+extension;
/** Opaque byte fixtures test filesystem integrity; real figure exports have separate integration checks. */
function exported(sources:Record<string,string>,generation:string,source=entry):ExportedFiles{
 const inputSHA256=sha(generation+JSON.stringify(sources));
 const html='<script type="application/json" id="figure-provenance">'+JSON.stringify({inputSHA256,sourceSHA256:sources,view:{source}})+'</script>';
 const png=new TextEncoder().encode('opaque PNG fixture '+generation),svg=['<svg>'+generation+'</svg>','<svg>scene '+generation+'</svg>'];
 return{png,svg,html,receipt:{inputSHA256,htmlSHA256:sha(html),pngSHA256:sha(png),svgSHA256:svg.map(svg=>sha(svg))}};
}
async function fixture(run:(root:string,inputs:{entry:string;sources:Record<string,string>;binaries:Record<string,string>})=>Promise<void>){
 const root=await mkdtemp(join(tmpdir(),'cedar-export-integrity-'));
 try{await mkdir(join(root,'dev/d2'),{recursive:true});await writeFile(join(root,entry),'a: A');await run(root,{entry,sources:{[entry]:sha('a: A')},binaries:{}});}
 finally{await rm(root,{recursive:true,force:true});}
}
test('receipt-last publication validates actual files and refuses a wrong expected input',async()=>{
 await fixture(async(root,inputs)=>{
  await writeFile(join(root,stem+'.html'),'obsolete browser export');
  const image=exported(inputs.sources,'first');await publishFigure(root,inputs,async()=>image);
  await verifyFigure(root,entry,image.receipt.inputSHA256);
  expect(await Bun.file(join(root,stem+'.html')).exists()).toBe(false);
  await expect(verifyFigure(root,entry,sha('different input'))).rejects.toThrow('Unexpected');
 });
});
test('interrupted exporter invalidates the old receipt without claiming old images as new',async()=>{
 await fixture(async(root,inputs)=>{
  await publishFigure(root,inputs,async()=>exported(inputs.sources,'old'));
  await expect(publishFigure(root,inputs,async()=>{throw new Error('Browser export interrupted');})).rejects.toThrow('interrupted');
  await expect(verifyFigure(root,entry)).rejects.toThrow();
  expect((await readFile(join(root,stem+'.png'))).length).toBeGreaterThan(0);
 });
});
test('native rename failure after the first output leaves no acceptable receipt',async()=>{
 await fixture(async(root,inputs)=>{
  await publishFigure(root,inputs,async()=>exported(inputs.sources,'old'));
  await unlink(join(root,stem+'.svg'));await mkdir(join(root,stem+'.svg'));
  await expect(publishFigure(root,inputs,async()=>exported(inputs.sources,'new'))).rejects.toThrow();
  expect(await readFile(join(root,stem+'.png'),'utf8')).toContain('new');
  await expect(verifyFigure(root,entry)).rejects.toThrow();
 });
});
test('missing artifacts and individually mixed outputs cannot pass the renderer receipt',async()=>{
 await fixture(async(root,inputs)=>{
  for(const extension of ['png','svg','scene-1.svg','html']){
   const image=exported(inputs.sources,'current');await publishFigure(root,inputs,async()=>image);
   await unlink(join(root,output(extension)));await expect(verifyFigure(root,entry)).rejects.toThrow();
   await publishFigure(root,inputs,async()=>image);await writeFile(join(root,output(extension)),'bytes from another export');
   await expect(verifyFigure(root,entry)).rejects.toThrow('hash mismatch');
  }
 });
});
test('complete output sets from another entry or generation cannot be relabelled',async()=>{
 await fixture(async(root,inputs)=>{
  await publishFigure(root,inputs,async()=>exported(inputs.sources,'old'));
  const original=await readFile(join(root,receiptArtifact(entry)),'utf8');
  const altered=JSON.parse(original);altered.entry='dev/d2/another.d2';await writeFile(join(root,receiptArtifact(entry)),JSON.stringify(altered));
  await expect(verifyFigure(root,entry)).rejects.toThrow('another figure');
  await writeFile(join(root,receiptArtifact(entry)),original);const mismatch=JSON.parse(original);mismatch.receipt.inputSHA256=sha('unrelated generation');await writeFile(join(root,receiptArtifact(entry)),JSON.stringify(mismatch));
  await expect(verifyFigure(root,entry)).rejects.toThrow('binding mismatch');
  await publishFigure(root,inputs,async()=>exported(inputs.sources,'current'));await writeFile(join(root,entry),'a: changed');
  await expect(verifyFigure(root,entry)).rejects.toThrow('changed');
 });
});
test('missing receipt fields, inconsistent provenance and extra SVGs refuse publication',async()=>{
 await fixture(async(root,inputs)=>{
  await expect(publishFigure(root,inputs,async()=>exported(inputs.sources,'wrong', 'dev/d2/other.d2'))).rejects.toThrow('binding mismatch');
  const image=exported(inputs.sources,'extra');await expect(publishFigure(root,inputs,async()=>({...image,svg:[...image.svg,'<svg/>']}))).rejects.toThrow('SVG output set');
  await publishFigure(root,inputs,async()=>image);const receipt=JSON.parse(await readFile(join(root,receiptArtifact(entry)),'utf8'));delete receipt.receipt.htmlSHA256;await writeFile(join(root,receiptArtifact(entry)),JSON.stringify(receipt));
  await expect(verifyFigure(root,entry)).rejects.toThrow();
 });
});

test('swapping a whole otherwise-valid output bundle cannot change the requested entry',async()=>{
 await fixture(async(root,inputs)=>{
  const other='dev/d2/other.d2',otherStem=other.slice(0,-3);await writeFile(join(root,other),'b: B');
  await publishFigure(root,inputs,async()=>exported(inputs.sources,'A'));
  const otherInputs={entry:other,sources:{[other]:sha('b: B')},binaries:{}};
  await publishFigure(root,otherInputs,async()=>exported(otherInputs.sources,'B',other));
  for(const extension of ['png','svg','scene-1.svg','html','json'])await writeFile(join(root,output(extension)),await readFile(join(root,extension==='html'?htmlArtifact(other):extension==='json'?receiptArtifact(other):otherStem+'.'+extension)));
  await expect(verifyFigure(root,entry)).rejects.toThrow('another figure');
 });
});
test('source mutation during export cannot publish a current receipt',async()=>{
 await fixture(async(root,inputs)=>{
  await expect(publishFigure(root,inputs,async()=>{await writeFile(join(root,entry),'changed during export');return exported(inputs.sources,'stale');})).rejects.toThrow('changed');
  await expect(verifyFigure(root,entry)).rejects.toThrow();
 });
});

test('old unlisted scenes refuse verification and successful publication removes owned leftovers',async()=>{
 await fixture(async(root,inputs)=>{
  const image=exported(inputs.sources,'current');await publishFigure(root,inputs,async()=>image);
  await writeFile(join(root,stem+'.scene-9.svg'),'<svg>obsolete</svg>');
  await expect(verifyFigure(root,entry)).rejects.toThrow('Unlisted');
  await publishFigure(root,inputs,async()=>image);await verifyFigure(root,entry);
 });
});
