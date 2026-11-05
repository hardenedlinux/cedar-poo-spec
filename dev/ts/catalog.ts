// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import * as v from 'valibot';
import type {Model} from '@openmbee/opensysml';
import type {FigureInput} from '@deterministic-engineering/render';
import {sha} from './sources';
const text=v.pipe(v.string(),v.minLength(1));
const natural=v.pipe(v.number(),v.integer(),v.minValue(0),v.check((value:number)=>Number.isSafeInteger(value)));
const Case=v.object({name:text,revision:text,expected:v.picklist(['allow','deny']),policy_ref:natural,entities_ref:natural});
const Manifest=v.object({manifest_kind:v.picklist(['raw','schema-bound']),cases:v.array(Case),revision_sources:v.record(v.string(),natural),schema_ref:v.optional(natural)});
const Envelope=v.object({format_version:v.literal(2),entries:v.record(text,v.unknown()),sources:v.object({policies:v.array(v.unknown()),entities:v.array(v.unknown()),schemas:v.array(v.unknown())})});
export const categories=['raw','schema-bound','evolution','artifacts','data'] as const;
export type Category=typeof categories[number];
export interface EntrySummary {readonly key:string;readonly symbol:string;readonly category:Category;readonly cases:number;readonly expectedAllow:number;readonly expectedDeny:number;readonly revisions:number;}
export interface CatalogSummary {readonly sha256:string;readonly bytes:number;readonly formatVersion:number;readonly entries:readonly EntrySummary[];readonly pools:{readonly policies:number;readonly entities:number;readonly schemas:number};}
/** A display projection of native Lean JSON, not a Cedar parser, authorizer or proof checker. */
export function observeCatalog(raw:string):CatalogSummary {
 const input:unknown=JSON.parse(raw),catalog=v.parse(Envelope,input),pools={policies:catalog.sources.policies.length,entities:catalog.sources.entities.length,schemas:catalog.sources.schemas.length};
 const inPool=(index:number,kind:keyof typeof pools)=>{if(index>=pools[kind])throw new Error(`Unbound ${kind} source reference: ${index}`);};
 const manifest=(value:unknown)=>{const m=v.parse(Manifest,value);for(const row of m.cases){inPool(row.policy_ref,'policies');inPool(row.entities_ref,'entities');if(m.revision_sources[row.revision]!==row.policy_ref)throw new Error('Revision does not bind the case policy source');}for(const ref of Object.values(m.revision_sources))inPool(ref,'policies');if(m.schema_ref!==undefined)inPool(m.schema_ref,'schemas');if(m.manifest_kind==='schema-bound'&&m.schema_ref===undefined)throw new Error('Missing schema reference');return m;};
 const entries=Object.entries(catalog.entries).map(([key,value]):EntrySummary=>{
  let category:Category='data',manifests:ReturnType<typeof manifest>[]=[];
  if(v.is(v.object({manifest_kind:v.unknown()}),value)){const m=manifest(value);category=m.manifest_kind;manifests=[m];}
  else if(v.is(v.object({before:v.unknown(),after:v.unknown()}),value)){category='evolution';manifests=[manifest(value.before),manifest(value.after)];}
  else if(Array.isArray(value)&&value.length>0&&value.some(row=>v.is(v.object({policy_ref:v.unknown()}),row))){category='artifacts';for(const row of v.parse(v.array(v.object({root:text,policy_ref:natural})),value))inPool(row.policy_ref,'policies');}
  const rows=manifests.flatMap(m=>m.cases);
  return {key,symbol:'entry_'+sha(key).slice(0,16),category,cases:rows.length,expectedAllow:rows.filter(row=>row.expected==='allow').length,expectedDeny:rows.filter(row=>row.expected==='deny').length,revisions:manifests.reduce((n,m)=>n+Object.keys(m.revision_sources).length,0)};
 });
 if(new Set(entries.map(entry=>entry.symbol)).size!==entries.length)throw new Error('Projected SysML identity collision');
 return {sha256:sha(raw),bytes:Buffer.byteLength(raw),formatVersion:catalog.format_version,entries,pools};
}
export function catalogSysML(catalog:CatalogSummary):string {
 const string=(value:string)=>JSON.stringify(value);
 return `// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Generated from native Lean catalog SHA256 ${catalog.sha256}; expectations are not issued decisions.
package LeanCatalog {
 private import ScalarValues::*;
 part def CatalogueGroup;
 attribute sourceSHA256 : String = ${string(catalog.sha256)};
 attribute entryCount : Integer = ${catalog.entries.length};
 attribute caseCount : Integer = ${catalog.entries.reduce((n,entry)=>n+entry.cases,0)};
 ${categories.map((category,index)=>`part group${index} : CatalogueGroup;\n attribute group${index}Count : Integer = ${catalog.entries.filter(entry=>entry.category===category).length};`).join('\n')}
 package Entries {
 ${catalog.entries.map(entry=>`part ${entry.symbol} {
 attribute entryKey : String = ${string(entry.key)};
 attribute category : String = ${string(entry.category)};
 attribute caseCount : Integer = ${entry.cases};
 attribute expectedAllow : Integer = ${entry.expectedAllow};
 attribute expectedDeny : Integer = ${entry.expectedDeny};
 attribute revisionCount : Integer = ${entry.revisions};
 }`).join('\n')}
 }
 view overview {${categories.map((_,index)=>`expose group${index};`).join(' ')}}
}`;
}

/** Catalog-specific annotations; generic SDK projection knows neither categories nor units. */
export const CatalogViewSchema=v.object({catalog:v.optional(v.strictObject({counts:v.record(text,v.strictObject({expression:text,category:v.picklist(categories),one:text,other:text}))}))});
export async function catalogCaptions(model:Pick<Model,'eval'>,author:Pick<FigureInput,'model'>,catalog:CatalogSummary|undefined,metadata:unknown){
 const counts=v.parse(CatalogViewSchema,metadata).catalog?.counts??{};
 const captions:Record<string,string>={},observations:{expression:string;value:string}[]=[];
 if(!catalog){if(Object.keys(counts).length)throw new Error('Catalog annotation requires captured native input');return{captions,observations};}
 for(const[id,binding]of Object.entries(counts)){
  const subject=author.model?.subjects.find(subject=>subject.id===id);
  if(!subject)throw new Error('Unbound catalog subject: '+id);
  const value=await model.eval(binding.expression);
  if(value.kind!=='int')throw new Error('Catalog count expression is not an integer');
  const expected=catalog.entries.filter(entry=>entry.category===binding.category).length;
  if(value.value!==BigInt(expected))throw new Error('Lean / SysML category count mismatch');
  observations.push({expression:binding.expression,value:value.value.toString()});
  captions[id]=(subject.label??subject.id)+'\n'+value.value.toString()+' '+(value.value===1n?binding.one:binding.other);
 }
 return{captions,observations};
}
