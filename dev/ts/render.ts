// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import {readFile,writeFile,mkdir,readdir} from 'node:fs/promises';
import {resolve,relative,basename} from 'node:path';
import {fileURLToPath} from 'node:url';
import * as v from 'valibot';
import {connectWasm,type Model} from '@openmbee/opensysml';
import {chromium,type Browser} from 'playwright';
import {composeFigure,composeHeading,defineDesign,type FigureInput,type FigureComposer} from '@deterministic-engineering/render';
import {captureOpenSysMLView} from '@deterministic-engineering/render/opensysml';
import {exportFigure} from '@deterministic-engineering/render/export';
import {ProjectionSchema,bindView} from './projection';
import {observeCatalog,catalogSysML,catalogCaptions,CatalogViewSchema} from './catalog';
import {ProofViewSchema,readProofMap,type ProofMap} from './proofs';
import {componentIllustrations} from './components/assurance';
import {captureIncidentStory,composeIncident,type IncidentStory} from './components/incident';
import {captureHostBoundary,composeHostBoundary,type HostBoundary} from './components/host-boundary';
import {captureDefenseArtwork,composeDefenseFlow,type DefenseArtwork} from './components/defense-flow';
import {captureFiles,repositoryPath,rendererDependency,sha} from './sources';
import rendererPackage from '@deterministic-engineering/render/package.json' with {type:'json'};
import {extendPresentationTheme,defaultPresentationTheme} from '@deterministic-engineering/render/presentation-theme';
import {figureSource,hostSources} from './inputs';
import {publishFigure} from './artifacts';
import {bindNotation,composeNotation} from './notation';
import {projectEntry,readProjectLayout,selectProjectModels} from './project';
import {captureFinancialArtwork,type FinancialArtwork} from './components/financial';
import {PaymentComponentSchema,composePayment,type PaymentComponent} from './components/payment';
const text=v.pipe(v.string(),v.minLength(1));
const compose=(artwork?:FinancialArtwork,component?:PaymentComponent,proofs?:ProofMap,story?:IncidentStory,defense?:DefenseArtwork,hostBoundary?:HostBoundary):FigureComposer=>context=>{
 if(!context.model)throw new Error('Missing projected SDK model');
 const illustrated=proofs&&proofs.cards.every(card=>/^(FinancialAttackers|WalletSigningProofs|TenantScenarioProofs|WalletHostProofs)::/.test(card.id))?componentIllustrations(context,proofs):undefined;
 const diagram=story&&defense&&artwork?composeDefenseFlow(context,defense,artwork,story):composeNotation(context,illustrated);
 const notes:ReturnType<typeof composeHeading>[]=[];
 const heading=(text:string,role:string,questionRef?:string)=>{const part=composeHeading(context,{role,text,questionRef});notes.push(part);return part.markup;};
 const header=heading(context.view.title,'title')+context.questions.map(question=>heading(question.text,'question',question.ref)).join('')+heading(context.copy('description'),'note');
 const footer=heading(context.copy('status'),'note');
 const identity=artwork&&component?composePayment(context,artwork,component):undefined;
 const narrative=story?composeIncident(context,story):hostBoundary?composeHostBoundary(context,hostBoundary):undefined;
 return{markup:(identity?.markup??'')+header+(narrative?.markup??'')+diagram.markup+footer,css:(narrative?.css??'')+(identity?.css??'')+'\n'+diagram.css+notes.map(note=>note.css).join('\n')+'[data-figure]{padding:var(--gutter)}[data-figure]>svg{margin-bottom:10px}'};
};
const root=fileURLToPath(new URL('../../',import.meta.url));
const inputPath=resolve(process.argv[2]??new URL('../.generated/lean-catalog.json',import.meta.url).pathname);
const generatedModel='dev/sysml/lean-catalog.sysml',producer='.lake/build/bin/caseManifestsNative';
const available:Record<string,string>={};
async function inventory(directory:string):Promise<void>{
 for(const entry of await readdir(resolve(root,directory),{withFileTypes:true})){
  const path=directory+'/'+entry.name;
  if(entry.isDirectory()&&!entry.name.startsWith('.'))await inventory(path);
  else if(entry.isFile()&&entry.name.endsWith('.d2'))Object.assign(available,await captureFiles(root,[path]));
 }
}
await inventory('dev/d2');
const commonPaths=[...await hostSources(root),projectEntry,'dev/Justfile','dev/package.json','dev/bun.lock','dev/tsconfig.json'];
const sharedSources=await captureFiles(root,commonPaths);
const renderer={specifier:rendererDependency(JSON.parse(sharedSources['dev/package.json']!)),name:rendererPackage.name,version:rendererPackage.version};
let browser:Browser|undefined;
const connection=await connectWasm();
try{
 const projectModel=(await connection.parseSources([[projectEntry,sharedSources[projectEntry]!]])).raiseForErrors();
 const layout=await readProjectLayout(projectModel);await projectModel.close();
 Object.assign(available,await captureFiles(root,layout.scenarioFigures));
 const declared=[...Object.keys(available).filter(path=>path.startsWith('dev/d2/')&&path.slice('dev/d2/'.length).indexOf('/')<0),...layout.scenarioFigures].sort();
 const entries=process.argv[3]?[process.argv[3]]:declared;
 for(const entry of entries)if(!declared.includes(entry))throw new Error('Figure is not declared by the project: '+entry);
 if(!entries.length)throw new Error('No D2 figure declarations');
 browser=await chromium.launch();for(const file of entries){
 const name=basename(file,'.d2'),{compiled,author}=await figureSource(root,available,file);
 const metadata:unknown=JSON.parse(v.parse(v.object({figure:text}),compiled.data).figure);
 const projection=v.parse(ProjectionSchema,metadata).sysml;
 const modelPaths=selectProjectModels(layout,[projection.source,...Object.values(author.references).filter(path=>path.endsWith('.sysml'))]);
 const usesCatalog=v.parse(CatalogViewSchema,metadata).catalog!==undefined||modelPaths.includes(generatedModel);
 let catalog:ReturnType<typeof observeCatalog>|undefined;
 let lean:{path:string;sha256:string;formatVersion:number;entries:number;pools:NonNullable<typeof catalog>['pools']}|undefined;
 const extraSources:Record<string,string>={},binaries:Record<string,string>={};
 const component=v.parse(PaymentComponentSchema,metadata).component;
 if(component&&projection.view!==(component.variant==='base'?'WalletSigningProofs::assurance':component.variant==='assurance'?'FinancialAttackers::assurance':component.variant==='host'?'WalletHostProofs::assurance':'PaymentDefenseFlow::defense'))throw new Error('Payment component differs from the selected scenario view');
 const artwork=component?await captureFinancialArtwork(root):undefined;
 if(artwork){Object.assign(extraSources,artwork.sources);Object.assign(binaries,artwork.binaries);}
 const story=component?.variant==='incident'?await captureIncidentStory(root):undefined;
 if(story){Object.assign(extraSources,story.sources);Object.assign(binaries,story.binaries);}
 const hostBoundary=component?.variant==='host'?await captureHostBoundary(root):undefined;
 if(hostBoundary)Object.assign(extraSources,hostBoundary.sources);
 const defense=story?await captureDefenseArtwork(root):undefined;
 if(defense){Object.assign(extraSources,defense.sources);Object.assign(binaries,defense.binaries);}
 if(usesCatalog){
  const path=relative(root,inputPath),raw=await readFile(await repositoryPath(root,path),'utf8');
  catalog=observeCatalog(raw);extraSources[path]=raw;
  await writeFile(resolve(root,generatedModel),catalogSysML(catalog));
  Object.assign(extraSources,await captureFiles(root,['Examples/ManifestCatalog.lean','CedarPooSpec/Transport/SourceCatalog.lean','lean-toolchain','lakefile.toml','lake-manifest.json']));
  binaries[producer]=sha(await readFile(await repositoryPath(root,producer)));
  lean={path,sha256:catalog.sha256,formatVersion:catalog.formatVersion,entries:catalog.entries.length,pools:catalog.pools};
 }
 const capturedModels=await captureFiles(root,modelPaths.filter(path=>path!==projectEntry));
 const modelSources=Object.fromEntries(modelPaths.map(path=>[path,path===projectEntry?sharedSources[projectEntry]!:capturedModels[path]!]));
 const model:Model=(await connection.parseSources(Object.entries(modelSources))).raiseForErrors();
 const capture=await captureOpenSysMLView(connection,model.hash,projection.view,{depth:1});
 const proofSelection=v.parse(ProofViewSchema,metadata).proofs;
 const proofClaims=proofSelection?await readProofMap(model,proofSelection.namespace):undefined;
 const {captions,observations}=await catalogCaptions(model,author,catalog,metadata);
 if(capture.requestedView!==projection.view||capture.modelHash!==model.hash)throw new Error('SDK model / view drift');
 const linked=bindView(author,capture,projection.bindings,captions);
 const capturePath=`dev/.generated/${name}-sdk.json`;const captureJSON=JSON.stringify(capture);
 await mkdir(resolve(root,'dev/.generated'),{recursive:true});await writeFile(resolve(root,capturePath),captureJSON);
 const sources:Record<string,string>={...sharedSources,...author.sources,...modelSources,...extraSources,[capturePath]:captureJSON};
 for(const path of [...Object.values(author.references),...(proofClaims?.cards.map(card=>card.source)??[])]){
  if(Object.hasOwn(sources,path))continue;
  sources[path]=await readFile(await repositoryPath(root,path),'utf8');
 }
 const metricBindings=v.parse(CatalogViewSchema,metadata).catalog?.counts??{};
 const metrics=Object.fromEntries(Object.entries(metricBindings).map(([id,binding])=>{
  const observed=observations.find(item=>item.expression===binding.expression);
  if(!observed)throw new Error('Missing SDK metric observation: '+id);
  return[id,Number(observed.value)];
 }));
 const presentation=bindNotation(author.presentation,linked.mapping,linked.model,linked.icons,proofClaims,metrics);
 const input:FigureInput={...author,theme:extendPresentationTheme(author.theme??defaultPresentationTheme,{typography:{labelSize:'13px'}}),sources,references:{...author.references,sdk:capturePath,...(lean?{catalog:lean.path}:{})},model:linked.model,modelSource:{ref:'sdk',modelHash:model.hash,view:projection.view},modelTrace:linked.trace,presentation,design:defineDesign({audience:'Cedar Library developers',medium:'repository documentation',message:author.view.title,questionRefs:author.questions.map(question=>question.ref),requiredSubjects:linked.model.subjects.map(node=>node.id),requiredRelations:linked.model.relations.map(edge=>edge.id),focalSubjects:[]})};
 const figure=composeFigure(input,compose(artwork,component,proofClaims,story,defense,hostBoundary));
 const fontRights:Readonly<Record<string,string>>={Kalam:'2014 Indian Type Foundry (info@indiantypefoundry.com)',Inter:'2016 The Inter Project Authors (https://github.com/rsms/inter)'};
 const fonts=[...new Set(figure.fonts.map(font=>font.family))];
 for(const font of fonts)if(!Object.hasOwn(fontRights,font))throw new Error('Declare actual rights before publishing a new font: '+font);
 await publishFigure(root,{entry:file,sources:figure.sourceSHA256,binaries,sdk:{modelHash:model.hash,view:projection.view,trace:linked.trace,diagnostics:model.diagnostics,observations},lean,proofClaims,renderer},
  ()=>exportFigure(figure,browser!,{scale:1.5,minimumTextSize:12,webp:false,attribution:{copyright:['2026 hardenedlinux Linux Team and Contributors',...fonts.map(font=>fontRights[font]!)],license:fonts.length?'Apache-2.0 AND OFL-1.1':'Apache-2.0'}}));
 console.log(name,{subjects:linked.model.subjects.length,relations:linked.model.relations.length,modelHash:model.hash});
}}finally{await browser?.close();await connection.close();}
