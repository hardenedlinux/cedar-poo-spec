// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {resources} from '../inputs';
import {readFile} from 'node:fs/promises';
import * as v from 'valibot';
import {compileModel,readD2Figure} from '@deterministic-engineering/render';
import type {OpenSysMLCapture} from '@deterministic-engineering/render/opensysml';
import {ProjectionSchema,bindView} from '../projection';
const root=new URL('../../',import.meta.url),file='dev/d2/security-frameworks.d2';
test('actual SDK identities and relationships bind independently of D2 enumeration',async()=>{
 const raw=await readFile(new URL(file,root),'utf8'),compiled=await compileModel({[file]:raw},file),author=readD2Figure(compiled,{[file]:raw},resources);
 const bindings=v.parse(ProjectionSchema,JSON.parse(v.parse(v.object({figure:v.string()}),compiled.data).figure)).sysml.bindings;
 const capture:OpenSysMLCapture=JSON.parse(await readFile(new URL('../.generated/security-frameworks-sdk.json',import.meta.url),'utf8'));
 const actual=bindView(author,capture,bindings);expect(actual.model.subjects).toHaveLength(5);expect(actual.model.relations).toHaveLength(4);expect(actual.trace.nodes.every(node=>node.origin?.file==='dev/sysml/security-frameworks.sysml')).toBe(true);
 const reordered={...capture,rendering:{...capture.rendering,nodes:[...capture.rendering.nodes].reverse()}};expect(bindView(author,reordered,bindings).model.relations).toEqual(actual.model.relations);
 const missing={...capture,rendering:{...capture.rendering,nodes:capture.rendering.nodes.slice(1)}};expect(()=>bindView(author,missing,bindings)).toThrow();
 const edgeMissing={...capture,rendering:{...capture.rendering,edges:capture.rendering.edges.slice(1)}};expect(()=>bindView(author,edgeMissing,bindings)).toThrow('omitted');
 const dangling={...capture,rendering:{...capture.rendering,edges:[{...capture.rendering.edges[0]!,to:'not-a-node'},...capture.rendering.edges.slice(1)]}};expect(()=>bindView(author,dangling,bindings)).toThrow('endpoint');
 expect(()=>bindView(author,capture,bindings,{missing:'invented'})).toThrow('Unbound display caption');
 const translated=bindView(author,capture,bindings,{core:'核心定义'});expect(translated.model.subjects.find(node=>node.id===translated.mapping.core)?.label).toBe('核心定义');
 expect(()=>v.parse(ProjectionSchema,{sysml:{source:'model',view:'v',bindings:{a:{name:'a',icon:'model',category:'raw'}}}})).toThrow();
 expect(()=>bindView(author,capture,{...bindings,extra:{name:'missing',icon:'model'}})).toThrow('binding');
},30000);
