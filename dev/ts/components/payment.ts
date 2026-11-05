// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import * as v from 'valibot';
import type {FigureContext} from '@deterministic-engineering/render';
import {composeFinancial,type FinancialArtwork} from './financial';
export const PaymentComponentSchema=v.object({component:v.optional(v.strictObject({kind:v.literal('payment'),variant:v.picklist(['base','incident','assurance','host'])}))});
export type PaymentComponent=NonNullable<v.InferOutput<typeof PaymentComponentSchema>['component']>;
/** Payment specializes the shared financial frame without copying any model or proof cards. */
export function composePayment(context:FigureContext,artwork:FinancialArtwork,selection:PaymentComponent){
 return composeFinancial(context,artwork,selection.variant==='incident'?'Payment · reported wallet attack scenario':'Payment · reusable wallet signing scenario',{label:'Original payment artwork',uri:artwork.images.payment});
}
