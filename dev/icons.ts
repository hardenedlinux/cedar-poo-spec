// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
import type {IconAsset} from '@deterministic-engineering/render/icons';
const glyph=(label:string,body:string):IconAsset=>({label,svg:`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">${body}</svg>`});
/** Local vector metaphors selected by the view; no imported bitmap or font icon. */
export const cedarIcons={
 caller:glyph('Caller requesting publication','<circle cx="32" cy="17" r="10"/><path d="M12 56V43a20 20 0 0 1 40 0v13M23 56V45M41 56V45"/>'),
 request:glyph('Request bound to its original contract','<rect x="7" y="9" width="32" height="43" rx="5"/><path d="M15 20h16M15 28h12M15 36h9"/><circle cx="45" cy="43" r="12"/><path d="M45 26v8M45 52v7M28 43h8M54 43h7"/>'),
 evidence:glyph('Selected review evidence','<path d="M12 6h29l10 10v38H12zM41 6v12h10M20 26h20M20 34h14"/><circle cx="39" cy="43" r="11"/><path d="m34 43 4 4 7-9"/>'),
 registry:glyph('Committed authority record','<ellipse cx="29" cy="14" rx="20" ry="8"/><path d="M9 14v31c0 11 40 11 40 0V14M9 28c0 11 40 11 40 0"/><path d="m36 44 7 7 13-15"/>'),
 recovery:glyph('Recovered record remains bound','<path d="M15 23a19 19 0 1 1-1 20M15 10v14H3"/><rect x="24" y="25" width="21" height="25" rx="3"/><path d="M30 32h9M30 39h9"/>'),
 registrar:glyph('Current registrar identity','<circle cx="23" cy="17" r="9"/><path d="M7 49v-8a16 16 0 0 1 32 0v8"/><circle cx="45" cy="34" r="7"/><path d="M45 41v16M45 48h9M45 54h6"/>'),
 current:glyph('Current-use security condition','<path d="M32 5 52 13v15c0 14-20 27-20 27S12 42 12 28V13z"/><circle cx="32" cy="28" r="10"/><path d="M32 21v7l6 4"/>'),
 pending:glyph('Command-specific pending intent','<rect x="8" y="10" width="30" height="44" rx="4"/><path d="M16 20h14M16 29h12"/><path d="M41 24h17M41 51h17M44 24v7l11 13v7M55 24v7L44 44v7"/>'),
 gate:glyph('Actual final commit boundary','<path d="M8 55V12h39v43M3 55h52M17 12V6h22v6M18 22h12M18 31h8"/><rect x="31" y="32" width="25" height="22" rx="4"/><path d="M36 32v-8a8 8 0 0 1 16 0v8"/><circle cx="44" cy="43" r="2"/>'),
 observer:glyph('Observer sees the installed image','<path d="M4 31s10-17 28-17 28 17 28 17-10 17-28 17S4 31 4 31z"/><circle cx="32" cy="31" r="9"/><path d="m28 31 3 3 6-7"/>')
} as const;
