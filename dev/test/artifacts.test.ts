// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {readFile,readdir} from 'node:fs/promises';
import {assertCurrent,rendererArchive,sha} from '../sources';
const root=new URL('../../',import.meta.url);
interface Receipt {binaries:Record<string,string>;sources:Record<string,string>;receipt:{drawing:string;pngSHA256:string;htmlSHA256:string;svgSHA256:string[];readability:{minimumTextSize:number}};sdk:{modelHash:string;view:string;trace:{modelHash:string}};lean:{path:string;sha256:string};rendererArchiveSHA256:string;}
for(const name of (await readdir(new URL('../d2/',import.meta.url))).filter(name=>name.endsWith('.d2')).map(name=>name.slice(0,-3)).sort())test(name+' output binds actual input bytes, SDK model and hand-drawn artifacts',async()=>{
 const base='dev/d2/'+name,receipt:Receipt=JSON.parse(await readFile(new URL(base+'.json',root),'utf8'));
 await assertCurrent(root.pathname,{...receipt.sources,...receipt.binaries});
 expect(sha(await readFile(new URL(base+'.png',root)))).toBe(receipt.receipt.pngSHA256);expect(sha(await readFile(new URL(base+'.svg',root)))).toBe(receipt.receipt.svgSHA256[0]!);expect(sha(await readFile(new URL(base+'.html',root)))).toBe(receipt.receipt.htmlSHA256);
 expect(receipt.receipt.drawing.startsWith('roughjs@')).toBe(true);expect(receipt.receipt.readability.minimumTextSize).toBeGreaterThanOrEqual(12);expect(receipt.sdk.modelHash).toBe(receipt.sdk.trace.modelHash);
 expect(receipt.lean.sha256).toBe(sha(await readFile(new URL(receipt.lean.path,root))));expect(receipt.rendererArchiveSHA256).toBe(sha(await readFile(new URL(rendererArchive(JSON.parse(await readFile(new URL('dev/package.json',root),'utf8'))),root))));
});
