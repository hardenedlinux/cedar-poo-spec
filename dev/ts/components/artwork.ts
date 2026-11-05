// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import sharp from 'sharp';
import {repositoryPath,sha} from '../sources';
export interface Artwork<Id extends string>{readonly images:Readonly<Record<Id,string>>;readonly sources:Readonly<Record<string,string>>;readonly binaries:Readonly<Record<string,string>>;}
/** Shared immutable-original capture for component families; no image generation at render time. */
export async function captureArtwork<const Ids extends readonly string[]>(root:string,manifestPath:string,ids:Ids,directory:string):Promise<Artwork<Ids[number]>>{
 const raw=await readFile(await repositoryPath(root,manifestPath),'utf8');
 const manifest=v.parse(v.object({formatVersion:v.literal(1),assets:v.array(v.object({id:v.string(),path:v.string(),sha256:v.string()}))}),JSON.parse(raw));
 if(new Set(manifest.assets.map(asset=>asset.id)).size!==manifest.assets.length||ids.some(id=>!manifest.assets.some(asset=>asset.id===id)))throw new Error('Artwork requires every distinct registered component');
 const images={} as Record<Ids[number],string>,binaries:Record<string,string>={};
 const selected=manifest.assets.filter(asset=>ids.includes(asset.id));
 // Bound native encoder concurrency; independent originals do not need serial encoding.
 for(let first=0;first<selected.length;first+=2)await Promise.all(selected.slice(first,first+2).map(async asset=>{
  if(asset.path!==`${directory}/${asset.id}.png`)throw new Error('Artwork path differs from its registered component');
  const bytes=await readFile(await repositoryPath(root,asset.path)),actual=sha(bytes);
  if(actual!==asset.sha256)throw new Error('Artwork differs from its generation manifest: '+asset.id);
  const compressed=await sharp(bytes,{failOn:'error'}).resize({width:1024,height:1024,fit:'inside',withoutEnlargement:true,kernel:sharp.kernel.lanczos3}).webp({quality:88,alphaQuality:100,effort:4,smartSubsample:true}).toBuffer();
  images[asset.id as Ids[number]]='data:image/webp;base64,'+compressed.toString('base64');binaries[asset.path]=actual;
 }));
 return{images,sources:{[manifestPath]:raw},binaries};
}
