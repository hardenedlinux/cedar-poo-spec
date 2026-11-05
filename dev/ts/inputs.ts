// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {resolve,relative} from 'node:path';
import {realpath} from 'node:fs/promises';
import {compileModel,readD2Figure} from '@deterministic-engineering/render';
import {captureFiles} from './sources';
import {engineeringIcons} from '@deterministic-engineering/render/icons';
import {cedarIcons} from './icons';
export const resources={iconPacks:{engineering:engineeringIcons,cedar:cedarIcons}};

/** References already belong to D2. The official compiler enforces a closed virtual FS. */
export async function figureSource(root:string,inventory:Readonly<Record<string,string>>,entry:string){
 const observed=await compileModel(inventory,entry),provisional=readD2Figure(observed,inventory,resources);
 const paths=[...new Set([entry,...Object.values(provisional.references).filter(path=>path.endsWith('.d2'))])].sort();
 const closed=await captureFiles(root,paths);
 // Identical closed bytes need no second native compiler invocation. This
 // reuses this call's observation only; missing/extra/imported bytes still close
 // through the official compiler, without a persistent cache or wider budget.
 const exact=Object.keys(inventory).length===paths.length&&paths.every(path=>inventory[path]===closed[path]);
 const compiled=exact?observed:await compileModel(closed,entry),author=readD2Figure(compiled,closed,resources);
 for(const path of Object.values(author.references).filter(path=>path.endsWith('.d2')))
  if(!Object.hasOwn(closed,path))throw new Error('D2 reference closure changed during compilation');
 return{compiled,author};
}

/** Bun, not a TS import parser or directory glob, observes the host's local module graph. */
export async function hostSources(root:string,entry='dev/ts/render.ts'):Promise<string[]>{
 const built=await Bun.build({entrypoints:[resolve(root,entry)],root,packages:'external',target:'bun',metafile:true});
 if(!built.success||!built.metafile)throw new Error('Cannot observe host module inputs: '+built.logs.join('\n'));
 const canonical=await realpath(root);
 return (await Promise.all(Object.keys(built.metafile.inputs).map(async path=>relative(canonical,await realpath(resolve(path)))))).sort();
}
