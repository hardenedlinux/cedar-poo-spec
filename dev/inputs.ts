// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {resolve,relative} from 'node:path';
import {realpath} from 'node:fs/promises';
import {compileModel,readD2Figure} from '@deterministic-engineering/render';
import {captureFiles} from './sources';

/** References already belong to D2. The official compiler enforces a closed virtual FS. */
export async function figureSource(root:string,inventory:Readonly<Record<string,string>>,entry:string){
 const provisional=readD2Figure(await compileModel(inventory,entry),inventory);
 const paths=[...new Set([entry,...Object.values(provisional.references).filter(path=>path.endsWith('.d2'))])].sort();
 const closed=await captureFiles(root,paths);
 const compiled=await compileModel(closed,entry),author=readD2Figure(compiled,closed);
 for(const path of Object.values(author.references).filter(path=>path.endsWith('.d2')))
  if(!Object.hasOwn(closed,path))throw new Error('D2 reference closure changed during compilation');
 return{compiled,author};
}

/** Bun, not a TS import parser or directory glob, observes the host's local module graph. */
export async function hostSources(root:string,entry='dev/render.ts'):Promise<string[]>{
 const built=await Bun.build({entrypoints:[resolve(root,entry)],root,packages:'external',target:'bun',metafile:true});
 if(!built.success||!built.metafile)throw new Error('Cannot observe host module inputs: '+built.logs.join('\n'));
 const canonical=await realpath(root);
 return (await Promise.all(Object.keys(built.metafile.inputs).map(async path=>relative(canonical,await realpath(resolve(path)))))).sort();
}
