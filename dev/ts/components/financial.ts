// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import {composeHeading,type FigureContext} from '@deterministic-engineering/render';
import {captureArtwork,type Artwork} from './artwork';
export type FinancialArtwork=Artwork<'financial'|'payment'>;
export const captureFinancialArtwork=(root:string)=>captureArtwork(root,'dev/assets/financial/artwork.json',['financial','payment'] as const,'dev/assets/financial');
/** Shared financial identity frame; all semantic text remains native vector headings. */
export function composeFinancial(context:FigureContext,artwork:FinancialArtwork,detail:string,companion?:{readonly label:string;readonly uri:string}){
 const title=composeHeading(context,{text:'Financial services',role:'note'});
 const subtitle=composeHeading(context,{text:detail,role:'note'});
 // Original raster artwork is embedded explicitly in SVG, never traced into fake vector paths.
 const illustration=`<svg xmlns="http://www.w3.org/2000/svg" data-vector-surface="" role="img" aria-label="Original financial artwork" width="${companion?264:132}" height="136" viewBox="0 0 ${companion?264:132} 136"><image href="${artwork.images.financial}" x="0" y="0" width="132" height="132"/>${companion?`<image aria-label="${context.text(companion.label)}" href="${companion.uri}" x="132" y="0" width="132" height="132"/>`:""}</svg>`;
 return{markup:`<section class="financial-component">${illustration}<div>${title.markup}${subtitle.markup}</div></section>`,css:title.css+'\n'+subtitle.css+'\n.financial-component{display:flex;align-items:center;gap:20px;margin:8px 0 16px}.financial-component>svg{flex:none}.financial-component>div{display:grid;gap:6px}'};
}
