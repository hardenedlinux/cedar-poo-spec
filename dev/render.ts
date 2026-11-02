// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {readFile,writeFile,mkdir,readdir} from 'node:fs/promises';
import {resolve,relative,basename} from 'node:path';
import {fileURLToPath} from 'node:url';
import * as v from 'valibot';
import {connectWasm,type Model} from '@openmbee/opensysml';
import {chromium,type Browser} from 'playwright';
import {compileModel,readD2Figure,composeFigure,composeDiagram,modelDiagram,composeHeading,defineDesign,type FigureInput,type FigureComposer} from '@deterministic-engineering/render';
import {captureOpenSysMLView} from '@deterministic-engineering/render/opensysml';
import {exportFigure} from '@deterministic-engineering/render/export';
import {ProjectionSchema,bindView} from './projection';
import {observeCatalog,catalogSysML,catalogCaptions} from './catalog';
import {ProofViewSchema,readProofMap} from './proofs';
import {assertCurrent,captureFiles,repositoryPath,rendererArchive,sha} from './sources';
const text=v.pipe(v.string(),v.minLength(1));
const compose:FigureComposer=context=>{
 if(!context.model)throw new Error('Missing projected SDK model');
 const diagram=composeDiagram(context,modelDiagram(context.model,context.presentation));
 const notes:ReturnType<typeof composeHeading>[]=[];
 const heading=(text:string,role:string,questionRef?:string)=>{const part=composeHeading(context,{role,text,questionRef});notes.push(part);return part.markup;};
 const header=heading(context.view.title,'title')+context.questions.map(question=>heading(question.text,'question',question.ref)).join('')+heading(context.copy('description'),'note');
 const label=(id:string)=>context.model!.subjects.find(node=>node.id===id)!.label?.split('\n')[0]??id;
 const legend=context.presentation&&typeof context.presentation==='object'&&'legend'in context.presentation&&context.presentation.legend===true?'<section class="legend">'+context.model.relations.map(edge=>'<div data-relation="'+context.text(edge.id)+'">'+heading(edge.label,'heading')+heading(label(edge.src)+' → '+label(edge.dst),'note')+'</div>').join('')+'</section>':'';
 const footer=heading(context.copy('status'),'note');
 return{markup:header+diagram.markup+legend+footer,css:diagram.css+notes.map(note=>note.css).join('\n')+'[data-figure]{padding:var(--gutter)}[data-figure]>svg{margin-bottom:10px}.legend{display:grid;grid-template-columns:1fr 1fr;gap:16px;margin:16px 0}.legend svg{margin-bottom:4px}'};
};
const root=fileURLToPath(new URL('../',import.meta.url));
const inputPath=resolve(process.argv[2]??new URL('.generated/lean-catalog.json',import.meta.url).pathname);
await repositoryPath(root,inputPath);
const raw=await readFile(inputPath,'utf8'),catalog=observeCatalog(raw),generated=catalogSysML(catalog);
await mkdir(resolve(root,'dev/sysml'),{recursive:true});await writeFile(resolve(root,'dev/sysml/lean-catalog.sysml'),generated);
let browser:Browser|undefined;
const entries=(await readdir(resolve(root,'dev/d2'))).filter(file=>file.endsWith('.d2')).sort();
if(!entries.length)throw new Error('No D2 figure declarations');
const d2Sources=await captureFiles(root,entries.map(file=>'dev/d2/'+file));
const adapters=(await readdir(resolve(root,'dev'))).filter(file=>file.endsWith('.ts')).map(file=>'dev/'+file);
const sourceFiles=[...adapters,'dev/Justfile','dev/package.json','dev/bun.lock','Examples/ManifestCatalog.lean','CedarPooSpec/Transport/SourceCatalog.lean','lean-toolchain','lakefile.toml','lake-manifest.json'];
const sharedSources=await captureFiles(root,sourceFiles);
const archive=rendererArchive(JSON.parse(sharedSources['dev/package.json']!)),producer='.lake/build/bin/caseManifestsNative';
const binaryHashes=Object.fromEntries(await Promise.all([archive,producer].map(async path=>[path,sha(await readFile(await repositoryPath(root,path)))])));
const connection=await connectWasm();
try{browser=await chromium.launch();for(const entry of entries){
 const name=basename(entry,'.d2'),file='dev/d2/'+entry;
 const compiled=await compileModel(d2Sources,file),author=readD2Figure(compiled,d2Sources);
 const metadata:unknown=JSON.parse(v.parse(v.object({figure:text}),compiled.data).figure);
 const projection=v.parse(ProjectionSchema,metadata).sysml;
 const modelBytes=await readFile(await repositoryPath(root,projection.source),'utf8');
 const model:Model=(await connection.parseSources([[projection.source,modelBytes]])).raiseForErrors();
 const capture=await captureOpenSysMLView(connection,model.hash,projection.view,{depth:1});
 const proofSelection=v.parse(ProofViewSchema,metadata).proofs;
 const proofClaims=proofSelection?await readProofMap(model,proofSelection.namespace):undefined;
 const {captions,observations}=await catalogCaptions(model,author,catalog,metadata);
 if(capture.requestedView!==projection.view||capture.modelHash!==model.hash)throw new Error('SDK model / view drift');
 const linked=bindView(author,capture,projection.bindings,captions);
 const capturePath=`dev/.generated/${name}-sdk.json`;const captureJSON=JSON.stringify(capture);
 await mkdir(resolve(root,'dev/.generated'),{recursive:true});await writeFile(resolve(root,capturePath),captureJSON);
 const sources:Record<string,string>={...sharedSources,...d2Sources,[projection.source]:modelBytes,[relative(root,inputPath)]:raw,[capturePath]:captureJSON};
 for(const path of [...Object.values(author.references),...(proofClaims?.cards.map(card=>card.source)??[])]){
  if(Object.hasOwn(sources,path))continue;
  sources[path]=await readFile(await repositoryPath(root,path),'utf8');
 }
 const input:FigureInput={...author,sources,references:{...author.references,sdk:capturePath,catalog:relative(root,inputPath)},model:linked.model,modelSource:{ref:'sdk',modelHash:model.hash,view:projection.view},modelTrace:linked.trace,presentation:{...(typeof author.presentation==='object'&&author.presentation?author.presentation:{}),icons:linked.icons},design:defineDesign({audience:'Cedar Library developers',medium:'repository documentation',message:author.view.title,questionRefs:author.questions.map(question=>question.ref),requiredSubjects:linked.model.subjects.map(node=>node.id),requiredRelations:linked.model.relations.map(edge=>edge.id),focalSubjects:[]})};
 const figure=composeFigure(input,compose);
 const fontRights:Readonly<Record<string,string>>={Kalam:'2014 Indian Type Foundry (info@indiantypefoundry.com)',Inter:'2016 The Inter Project Authors (https://github.com/rsms/inter)'};
 const fonts=[...new Set(figure.fonts.map(font=>font.family))];
 for(const font of fonts)if(!Object.hasOwn(fontRights,font))throw new Error('Declare actual rights before publishing a new font: '+font);
 const image=await exportFigure(figure,browser,{scale:1.5,minimumTextSize:12,attribution:{copyright:['2026 hardenedlinux Linux Team and Contributors',...fonts.map(font=>fontRights[font]!)],license:fonts.length?'Apache-2.0 AND OFL-1.1':'Apache-2.0'}});
 await assertCurrent(root,{...figure.sourceSHA256,...binaryHashes});
 const base=resolve(root,`dev/d2/${name}`);
 for(const [extension,data]of [['png',image.png],['svg',image.svg[0]!],['html',image.html]] as const)await writeFile(base+'.'+extension,data);
 await writeFile(base+'.json',JSON.stringify({sources:figure.sourceSHA256,receipt:image.receipt,sdk:{modelHash:model.hash,view:projection.view,trace:linked.trace,diagnostics:model.diagnostics,observations},lean:{path:relative(root,inputPath),sha256:catalog.sha256,formatVersion:catalog.formatVersion,entries:catalog.entries.length,pools:catalog.pools},proofClaims,binaries:binaryHashes,rendererArchiveSHA256:binaryHashes[archive]},null,2)+'\n');
 console.log(name,{subjects:linked.model.subjects.length,relations:linked.model.relations.length,minimumTextSize:image.receipt.readability.minimumTextSize,modelHash:model.hash});
}}finally{await browser?.close();await connection.close();}
await assertCurrent(root,binaryHashes);
if(sha(await readFile(inputPath))!==catalog.sha256)throw new Error('Lean input changed during rendering');
