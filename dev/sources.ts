// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {readFile,realpath} from 'node:fs/promises';
import {resolve,relative,isAbsolute} from 'node:path';
import * as v from 'valibot';
import {createHash} from 'node:crypto';
export const sha=(value:string|Uint8Array)=>createHash('sha256').update(value).digest('hex');

/** Host filesystem boundary only; the renderer still owns figure fingerprints. */
export async function repositoryPath(root:string,path:string):Promise<string>{
 const target=await realpath(resolve(root,path)),base=await realpath(root),name=relative(base,target);
 if(!name||isAbsolute(name)||name==='..'||name.startsWith('../'))throw new Error('Source escapes repository: '+path);
 return target;
}
export async function captureFiles(root:string,paths:readonly string[]):Promise<Record<string,string>>{
 const captured:Record<string,string>={};
 for(const path of paths)captured[path]=await readFile(await repositoryPath(root,path),'utf8');
 return captured;
}
/** Missing files and any content change invalidate publication; no stale fallback. */
export async function assertCurrent(root:string,hashes:Readonly<Record<string,string>>):Promise<void>{
 for(const[path,expected]of Object.entries(hashes)){
  const actual=sha(await readFile(await repositoryPath(root,path)));
  if(actual!==expected)throw new Error('Captured source changed before publication: '+path);
 }
}

/** Bun owns specifier resolution; the existing manifest remains its sole declaration. */
export function rendererDependency(manifest:unknown):string{
 const {dependencies}=v.parse(v.object({dependencies:v.object({'@deterministic-engineering/render':v.pipe(v.string(),v.minLength(1))})}),manifest);
 return dependencies['@deterministic-engineering/render'];
}
