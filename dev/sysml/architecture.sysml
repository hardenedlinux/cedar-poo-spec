// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Ownership/composition views; not an exhaustive import graph or a runtime trace.
package CedarArchitecture {
 private import Views::*;
 part def Component; part def VerticalControls; part def PlatformProjection; part def Foundation; part def Consumer;
 part leanPoo : Foundation;
 part cedar : Foundation;
 part model : Component;
 part zeroTrust : Component;
 part verticalControls : VerticalControls;
 part platformProjections : PlatformProjection;
 part production : Consumer;
 part examples : Consumer;
 part rust : Consumer;
 part host : Consumer;
 part functional : Component;
 part authorization : Component;
 part pseudonymization : Component;
 part admission : Component;
 part governance : Component;
 part gateway : Component;
 part data : Component;
 part cloud : Component;
 part agenticAI : Component;
 part health : VerticalControls;
 part finance : VerticalControls;
 part aws : PlatformProjection;
 part google : PlatformProjection;
 connection relation0 connect leanPoo to model;
 connection relation1 connect cedar to model;
 connection relation2 connect model to zeroTrust;
 connection relation3 connect model to verticalControls;
 connection relation4 connect model to platformProjections;
 connection relation5 connect model to production;
 connection relation6 connect model to examples;
 connection relation7 connect zeroTrust to production;
 connection relation8 connect zeroTrust to examples;
 connection relation9 connect verticalControls to production;
 connection relation10 connect platformProjections to production;
 connection relation11 connect production to rust;
 connection relation12 connect examples to rust;
 connection relation13 connect rust to host;
 view overview {
  expose leanPoo;
  expose cedar;
  expose model;
  expose zeroTrust;
  expose verticalControls;
  expose platformProjections;
  expose production;
  expose examples;
  expose rust;
  expose host;
  expose relation0;
  expose relation1;
  expose relation2;
  expose relation3;
  expose relation4;
  expose relation5;
  expose relation6;
  expose relation7;
  expose relation8;
  expose relation9;
  expose relation10;
  expose relation11;
  expose relation12;
  expose relation13;
  render asInterconnectionDiagram;
 }
 view components {
  expose functional;
  expose zeroTrust;
  expose authorization;
  expose pseudonymization;
  expose admission;
  expose governance;
  expose gateway;
  expose data;
  expose cloud;
  expose agenticAI;
  render asInterconnectionDiagram;
 }
 view verticalsPlatforms {
  expose health;
  expose finance;
  expose aws;
  expose google;
  render asInterconnectionDiagram;
 }
}
