// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {test,expect} from 'bun:test';
import {chromium} from 'playwright';
import {readFile,writeFile,mkdir,mkdtemp,rm} from 'node:fs/promises';
import {dirname,join} from 'node:path';
import {tmpdir} from 'node:os';
import {captureDefenseArtwork} from '../components/defense-flow';
import {captureIncidentStory} from '../components/incident';
import {captureFinancialArtwork} from '../components/financial';
import {verifyFigure,htmlArtifact,receiptArtifact} from '../artifacts';
const root=new URL('../../../',import.meta.url);
test('actual payment exports retain source-bound model labels and embed both original artwork assets',async()=>{
 const artwork=await captureFinancialArtwork(root.pathname);
 for(const name of ['Base','Binance2026','Binance2026Assurance']){
  const entry=`Examples/Scenarios/FinancialServices/Wallet/${name}.d2`,stem=entry.slice(0,-3);
  const receipt=await verifyFigure(root.pathname,entry);
  const story=name==='Binance2026'?await captureIncidentStory(root.pathname):undefined;
  const defense=story?await captureDefenseArtwork(root.pathname):undefined;
  expect(receipt.binaries).toEqual({...artwork.binaries,...story?.binaries,...defense?.binaries});
  const svg=await readFile(new URL(stem+'.svg',root),'utf8');
  for(const uri of Object.values(artwork.images))expect(svg.includes(uri)).toBe(true);
  expect(svg).toContain('Financial services');
  expect(svg).toContain('data-heading-role');
  expect(svg).not.toContain('foreignObject');
  const claims=JSON.parse(await readFile(new URL(receiptArtifact(entry),root),'utf8')).proofClaims;
  if(story&&defense){
   expect(story.defense).toEqual({deployment_refused:true,valid_transfer_released:true});
   expect(claims.cards.find((card:{id:string})=>card.id==='PaymentDefenseFlow::refused')).toMatchObject({role:'Definition',symbol:'CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release'});
   for(const [id,uri] of Object.entries(story.images)){expect(svg).toContain('data-incident-scene="'+id+'"');expect(svg.includes(uri)).toBe(true);}
   for(const uri of Object.values(defense.images))expect(svg.includes(uri)).toBe(true);
   expect(svg.includes('data-flow-observation="deployment_refused"')).toBe(true);
   expect(svg).toContain('data-flow-state="refused"');
   expect(svg).toContain('data-flow-state="required-inactive"');
   expect(svg).toContain('NOT REACHED');expect(svg).toContain('NO SIGNATURE');
   expect(svg).not.toContain('KERNEL THEOREM');
   const displayed=[...svg.matchAll(/data-defense-component="([^"]+)"/g)].map(match=>match[1]);
   expect(displayed.length).toBe(claims.cards.length);
   expect(new Set(displayed).size).toBe(claims.cards.length);
  }else{
   expect(svg).toContain('KERNEL THEOREM');expect(svg).toContain('HOST PREMISE');
   const illustrations=[...svg.matchAll(/data-component-illustration="([^"]+)"/g)].map(match=>match[1]);
   expect(illustrations.length).toBe(claims.cards.length);
   expect(new Set(illustrations).size).toBe(claims.cards.length);
   for(const card of claims.cards)expect(svg).toContain('data-lean-symbol="'+card.symbol+'"');
  }
 }
},30000);
test('changing an original image invalidates a restored real scenario export and refuses recomposition',async()=>{
 const entry='Examples/Scenarios/FinancialServices/Wallet/Base.d2',stem=entry.slice(0,-3);
 const receipt=await verifyFigure(root.pathname,entry);
 const temporary=await mkdtemp(join(tmpdir(),'cedar-financial-artwork-'));
 const copy=async(path:string)=>{await mkdir(dirname(join(temporary,path)),{recursive:true});await writeFile(join(temporary,path),await readFile(new URL(path,root)));};
 try{
  for(const path of [...Object.keys(receipt.sources),...Object.keys(receipt.binaries),receiptArtifact(entry),stem+'.png',htmlArtifact(entry),...receipt.receipt.svgSHA256.map((_,index)=>stem+(index?'.scene-'+index: '')+'.svg')])await copy(path);
  await verifyFigure(temporary,entry);
  const image='dev/assets/financial/payment.png';
  await writeFile(join(temporary,image),'unrelated image bytes');
  await expect(verifyFigure(temporary,entry)).rejects.toThrow('changed');
  await expect(captureFinancialArtwork(temporary)).rejects.toThrow('generation manifest');
  await copy(image);await verifyFigure(temporary,entry);
 }finally{await rm(temporary,{recursive:true,force:true});}
},30000);

test('compressed artwork retains alpha and source originals while reducing embedded bytes',async()=>{
 const artwork=await captureFinancialArtwork(root.pathname),browser=await chromium.launch();
 try{
 const page=await browser.newPage();
 for(const [id,uri] of Object.entries(artwork.images)){
  expect(uri.startsWith('data:image/webp;base64,')).toBe(true);
  const original=await readFile(new URL('dev/assets/financial/'+id+'.png',root));
  const compressed=Buffer.from(uri.slice(uri.indexOf(',')+1),'base64');
  const decoded=await page.evaluate(async({original,encoded})=>{
   const read=async(source:string)=>{const image=new Image();image.src=source;await image.decode();const canvas=document.createElement('canvas');canvas.width=image.naturalWidth;canvas.height=image.naturalHeight;const context=canvas.getContext('2d')!;context.drawImage(image,0,0);return{width:canvas.width,height:canvas.height,pixels:context.getImageData(0,0,canvas.width,canvas.height).data};};
   const before=await read(original),after=await read(encoded);let alphaEqual=before.pixels.length===after.pixels.length;
   for(let i=3;alphaEqual&&i<before.pixels.length;i+=4)if(before.pixels[i]!==after.pixels[i])alphaEqual=false;
   return{before:{width:before.width,height:before.height},after:{width:after.width,height:after.height},alphaEqual};
  },{original:'data:image/png;base64,'+original.toString('base64'),encoded:uri});
  expect(decoded.after).toEqual(decoded.before);expect(decoded.alphaEqual).toBe(true);
  expect(compressed.length).toBeLessThan(original.length/4);
 }
 }finally{await browser.close();}
 const entry='Examples/Scenarios/FinancialServices/Wallet/Binance2026.d2';
 await verifyFigure(root.pathname,entry);
 expect((await readFile(new URL(entry.slice(0,-3)+'.svg',root))).length).toBeLessThan(5*1024*1024);
 expect(await Bun.file(new URL(entry.slice(0,-3)+'.json',root)).exists()).toBe(false);
},30000);
