// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

import type {Model,SysMLValue} from '@openmbee/opensysml';
export const projectEntry='Project.sysml';
export interface ProjectLayout {
 readonly typescriptRoot:string;readonly sysmlRoot:string;readonly quintRoot:string;
 readonly modelSources:readonly string[];readonly scenarioFigures:readonly string[];
}
function text(value:SysMLValue):string{
 if(value.kind!=='string'||!value.value.trim())throw new Error('Project entry requires a nonempty SDK string');
 return value.value;
}
/** The official SDK owns SysML parsing, name resolution and attribute values. */
export async function readProjectLayout(model:Pick<Model,'eval'>):Promise<ProjectLayout>{
 const typescriptRoot=text(await model.eval('CedarProject::typescriptRoot'));
 const sysmlRoot=text(await model.eval('CedarProject::sysmlRoot'));
 const quintRoot=text(await model.eval('CedarProject::quintRoot'));
 if(typescriptRoot!=='dev/ts'||sysmlRoot!=='dev/sysml'||quintRoot!=='dev/qnt')throw new Error('Project development roots do not match their declared owners');
 const sources=await model.eval('CedarProject::modelSources');
 if(sources.kind!=='sequence')throw new Error('Project model sources must be an SDK sequence');
 const modelSources=sources.elements.map(text);
 if(!modelSources.length||new Set(modelSources).size!==modelSources.length)throw new Error('Project model source inventory is empty or duplicated');
 for(const source of modelSources){
  if(!source.startsWith(sysmlRoot+'/')||!source.endsWith('.sysml')||source.split('/').some(part=>!part||part==='.'||part==='..'))throw new Error('Project SysML source escapes its owner: '+source);
 }
 const figures=await model.eval('CedarProject::scenarioFigures');
 if(figures.kind!=='sequence')throw new Error('Project scenario figures must be an SDK sequence');
 const scenarioFigures=figures.elements.map(text);
 if(!scenarioFigures.length||new Set(scenarioFigures).size!==scenarioFigures.length)throw new Error('Scenario figure inventory is empty or duplicated');
 for(const path of scenarioFigures)if(!path.startsWith('Examples/Scenarios/')||!path.endsWith('.d2')||path.split('/').some(part=>!part||part==='.'||part==='..'))throw new Error('Scenario figure escapes its owner: '+path);
 return{typescriptRoot,sysmlRoot,quintRoot,modelSources,scenarioFigures};
}
export function selectProjectModels(layout:ProjectLayout,sources:readonly string[]):string[]{
 for(const source of sources)if(!layout.modelSources.includes(source))throw new Error('SysML source is not declared by Project.sysml: '+source);
 return [...new Set([projectEntry,...sources])].sort();
}
