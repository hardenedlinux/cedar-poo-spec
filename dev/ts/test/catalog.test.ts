// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {test,expect} from 'bun:test';
import {readFile} from 'node:fs/promises';
import {connectWasm,type Model} from '@openmbee/opensysml';
import type {FigureInput} from '@deterministic-engineering/render';
import {observeCatalog,catalogSysML,categories,catalogCaptions} from '../catalog';
const input=()=>({format_version:2,sources:{policies:[{}],entities:[[]],schemas:[{}]},entries:{example:{manifest_kind:'schema-bound',schema_ref:0,revision_sources:{r:0},cases:[{name:'case',revision:'r',policy_ref:0,entities_ref:0,expected:'deny'}]}}});
test('display observations retain source references and never promote expected decisions',()=>{
 const result=observeCatalog(JSON.stringify(input()));expect(result.entries[0]!.expectedDeny).toBe(1);expect(result.entries[0]!.expectedAllow).toBe(0);expect(result.entries[0]!.category).toBe('schema-bound');
 const malformed=input();malformed.entries.example.cases[0]!.policy_ref=4;expect(()=>observeCatalog(JSON.stringify(malformed))).toThrow('source reference');
 const drift=input();drift.entries.example.revision_sources.r=1;expect(()=>observeCatalog(JSON.stringify(drift))).toThrow('Revision');
 const missing=input();delete(missing.entries.example as {schema_ref?:number}).schema_ref;expect(()=>observeCatalog(JSON.stringify(missing))).toThrow('schema reference');
 expect(()=>observeCatalog(JSON.stringify({...input(),format_version:999}))).toThrow();
 expect(()=>observeCatalog(JSON.stringify({...input(),entries:{artifact:[{root:'broken',policy_ref:-1}]}}))).toThrow();
 expect(()=>observeCatalog(JSON.stringify({...input(),entries:{artifact:[{root:'broken',policy_ref:4}]}}))).toThrow('source reference');
 const data=observeCatalog(JSON.stringify({...input(),entries:{domain:[{business:'uninterpreted'}]}}));expect(data.entries[0]!.category).toBe('data');
});
test('actual Lean catalog becomes a parsed SDK model and category values round-trip',async()=>{
 const raw=await readFile(new URL('../../.generated/lean-catalog.json',import.meta.url),'utf8'),summary=observeCatalog(raw),source=catalogSysML(summary),connection=await connectWasm();
 try{
  const model=(await connection.parseSources([['dev/sysml/lean-catalog.sysml',source]])).raiseForErrors();
  const count=await model.eval('LeanCatalog::entryCount');expect(count.kind).toBe('int');if(count.kind==='int')expect(count.value).toBe(BigInt(summary.entries.length));
  for(const[order,category]of categories.entries()){const value=await model.eval(`LeanCatalog::group${order}Count`);expect(value.kind).toBe('int');if(value.kind==='int')expect(value.value).toBe(BigInt(summary.entries.filter(entry=>entry.category===category).length));}
  const view=await connection.renderView(model.hash,'LeanCatalog::overview',{depth:1});expect(view.nodes).toHaveLength(5);
  const broken=await connection.loads('package Broken { part ;');expect(broken.ok).toBe(false);expect(()=>broken.raiseForErrors()).toThrow();
 }finally{await connection.close();}
},30000);

test('catalog annotations validate native counts and keep display units in D2',async()=>{
 const catalog=observeCatalog(JSON.stringify(input())),author:Pick<FigureInput,'model'>={model:{subjects:[{id:'group',type:'rectangle',label:'范围'}],relations:[]}};
 const metadata={catalog:{counts:{group:{expression:'Count',category:'schema-bound',one:'个条目',other:'个条目'}}}};
 const model:Pick<Model,'eval'>={eval:async()=>({kind:'int',value:1n})};
 expect((await catalogCaptions(model,author,catalog,metadata)).captions.group).toBe('范围\n1 个条目');
 const two=input();const doubled=observeCatalog(JSON.stringify({...two,entries:{a:two.entries.example,b:two.entries.example}}));
 expect((await catalogCaptions({eval:async()=>({kind:'int',value:2n})},author,doubled,{catalog:{counts:{group:{expression:'Count',category:'schema-bound',one:'item',other:'items'}}}})).captions.group).toBe('范围\n2 items');
 expect(await catalogCaptions(model,author,catalog,{})).toEqual({captions:{},observations:[]});
 await expect(catalogCaptions({eval:async()=>({kind:'int',value:2n})},author,catalog,metadata)).rejects.toThrow('mismatch');
 await expect(catalogCaptions({eval:async()=>({kind:'string',value:'1'})},author,catalog,metadata)).rejects.toThrow('not an integer');
 await expect(catalogCaptions(model,{model:{subjects:[],relations:[]}},catalog,metadata)).rejects.toThrow('Unbound');
 await expect(catalogCaptions(model,author,catalog,{catalog:{counts:{group:{expression:'Count',category:'invented',one:'x',other:'y'}}}})).rejects.toThrow();
 await expect(catalogCaptions(model,author,catalog,{catalog:{counts:{group:{expression:'Count',category:'raw'}}}})).rejects.toThrow();
});
