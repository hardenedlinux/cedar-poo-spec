// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import {repositoryPath,sha} from '../sources';
export interface Artwork<Id extends string>{readonly images:Readonly<Record<Id,string>>;readonly sources:Readonly<Record<string,string>>;readonly binaries:Readonly<Record<string,string>>;}
/** Shared immutable-original capture for component families; no image generation at render time. */
export async function captureArtwork<const Ids extends readonly string[]>(root:string,manifestPath:string,ids:Ids,directory:string):Promise<Artwork<Ids[number]>>{
 const raw=await readFile(await repositoryPath(root,manifestPath),'utf8');
 const manifest=v.parse(v.object({formatVersion:v.literal(1),assets:v.array(v.object({id:v.string(),path:v.string(),sha256:v.string()}))}),JSON.parse(raw));
 if(manifest.assets.length!==ids.length||new Set(manifest.assets.map(asset=>asset.id)).size!==ids.length||manifest.assets.some(asset=>!ids.includes(asset.id)))throw new Error('Artwork requires every distinct registered component');
 const images={} as Record<Ids[number],string>,binaries:Record<string,string>={};
 for(const asset of manifest.assets){
  if(asset.path!==`${directory}/${asset.id}.png`)throw new Error('Artwork path differs from its registered component');
  const bytes=await readFile(await repositoryPath(root,asset.path)),actual=sha(bytes);
  if(actual!==asset.sha256)throw new Error('Artwork differs from its generation manifest: '+asset.id);
  images[asset.id as Ids[number]]='data:image/png;base64,'+bytes.toString('base64');binaries[asset.path]=actual;
 }
 return{images,sources:{[manifestPath]:raw},binaries};
}
