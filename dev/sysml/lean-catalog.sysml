// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Generated from native Lean catalog SHA256 c6856fdb9e8b2d36407b8605756659e8a1c02fca09ce628bc41c845f0e376657; expectations are not issued decisions.
package LeanCatalog {
 private import ScalarValues::*;
 part def CatalogueGroup;
 attribute sourceSHA256 : String = "c6856fdb9e8b2d36407b8605756659e8a1c02fca09ce628bc41c845f0e376657";
 attribute entryCount : Integer = 51;
 attribute caseCount : Integer = 1292;
 part group0 : CatalogueGroup;
 attribute group0Count : Integer = 24;
part group1 : CatalogueGroup;
 attribute group1Count : Integer = 23;
part group2 : CatalogueGroup;
 attribute group2Count : Integer = 1;
part group3 : CatalogueGroup;
 attribute group3Count : Integer = 1;
part group4 : CatalogueGroup;
 attribute group4Count : Integer = 2;
 package Entries {
 part entry_570cd03dd126b40c {
 attribute entryKey : String = "agent-chain";
 attribute category : String = "raw";
 attribute caseCount : Integer = 52;
 attribute expectedAllow : Integer = 45;
 attribute expectedDeny : Integer = 7;
 attribute revisionCount : Integer = 6;
 }
part entry_0fa3e4a07af4507e {
 attribute entryKey : String = "agent-data-flow";
 attribute category : String = "raw";
 attribute caseCount : Integer = 32;
 attribute expectedAllow : Integer = 24;
 attribute expectedDeny : Integer = 8;
 attribute revisionCount : Integer = 9;
 }
part entry_ac3fa65dbf8a0cce {
 attribute entryKey : String = "agent-data-flow-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 34;
 attribute expectedAllow : Integer = 24;
 attribute expectedDeny : Integer = 10;
 attribute revisionCount : Integer = 10;
 }
part entry_46c3f3f7154bb220 {
 attribute entryKey : String = "agent-delegation";
 attribute category : String = "raw";
 attribute caseCount : Integer = 33;
 attribute expectedAllow : Integer = 21;
 attribute expectedDeny : Integer = 12;
 attribute revisionCount : Integer = 8;
 }
part entry_1677398597752c08 {
 attribute entryKey : String = "agent-payment";
 attribute category : String = "raw";
 attribute caseCount : Integer = 34;
 attribute expectedAllow : Integer = 25;
 attribute expectedDeny : Integer = 9;
 attribute revisionCount : Integer = 8;
 }
part entry_97aa9727ea8ed12b {
 attribute entryKey : String = "agent-payment-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 32;
 attribute expectedAllow : Integer = 23;
 attribute expectedDeny : Integer = 9;
 attribute revisionCount : Integer = 8;
 }
part entry_6f0e9ea81d37ede9 {
 attribute entryKey : String = "agentic-ai-language-model-health-disclosure";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 20;
 attribute expectedAllow : Integer = 6;
 attribute expectedDeny : Integer = 14;
 attribute revisionCount : Integer = 4;
 }
part entry_13a87448ed488917 {
 attribute entryKey : String = "attested";
 attribute category : String = "raw";
 attribute caseCount : Integer = 13;
 attribute expectedAllow : Integer = 4;
 attribute expectedDeny : Integer = 9;
 attribute revisionCount : Integer = 3;
 }
part entry_fddc4c7eadc64b02 {
 attribute entryKey : String = "attested-schema-evolution";
 attribute category : String = "evolution";
 attribute caseCount : Integer = 12;
 attribute expectedAllow : Integer = 2;
 attribute expectedDeny : Integer = 10;
 attribute revisionCount : Integer = 2;
 }
part entry_e5e238923d2648e0 {
 attribute entryKey : String = "attested-views-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 13;
 attribute expectedAllow : Integer = 4;
 attribute expectedDeny : Integer = 9;
 attribute revisionCount : Integer = 3;
 }
part entry_33776141fc836bc5 {
 attribute entryKey : String = "australian-emr-upload";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 17;
 attribute expectedAllow : Integer = 4;
 attribute expectedDeny : Integer = 13;
 attribute revisionCount : Integer = 4;
 }
part entry_b89decfa030f0dda {
 attribute entryKey : String = "bounded-session";
 attribute category : String = "raw";
 attribute caseCount : Integer = 58;
 attribute expectedAllow : Integer = 21;
 attribute expectedDeny : Integer = 37;
 attribute revisionCount : Integer = 7;
 }
part entry_7d64a479cb932e88 {
 attribute entryKey : String = "claim-settlement-banking";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 56;
 attribute expectedAllow : Integer = 55;
 attribute expectedDeny : Integer = 1;
 attribute revisionCount : Integer = 2;
 }
part entry_caf38d42e2d88c68 {
 attribute entryKey : String = "claim-settlement-claims";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 28;
 attribute expectedAllow : Integer = 24;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 2;
 }
part entry_b9a81a6b2d4e1037 {
 attribute entryKey : String = "claim-settlement-handoff";
 attribute category : String = "data";
 attribute caseCount : Integer = 0;
 attribute expectedAllow : Integer = 0;
 attribute expectedDeny : Integer = 0;
 attribute revisionCount : Integer = 0;
 }
part entry_98569e7e9080addd {
 attribute entryKey : String = "clinical";
 attribute category : String = "raw";
 attribute caseCount : Integer = 14;
 attribute expectedAllow : Integer = 4;
 attribute expectedDeny : Integer = 10;
 attribute revisionCount : Integer = 2;
 }
part entry_01738f6269b969e6 {
 attribute entryKey : String = "country-approval";
 attribute category : String = "raw";
 attribute caseCount : Integer = 13;
 attribute expectedAllow : Integer = 9;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 4;
 }
part entry_673283083fc1bd8d {
 attribute entryKey : String = "country-approval-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 13;
 attribute expectedAllow : Integer = 9;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 4;
 }
part entry_72186d2b76628b03 {
 attribute entryKey : String = "cross-agent-egress-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 20;
 attribute expectedAllow : Integer = 14;
 attribute expectedDeny : Integer = 6;
 attribute revisionCount : Integer = 6;
 }
part entry_64d470d54b5bac39 {
 attribute entryKey : String = "delegated-approval";
 attribute category : String = "raw";
 attribute caseCount : Integer = 10;
 attribute expectedAllow : Integer = 1;
 attribute expectedDeny : Integer = 9;
 attribute revisionCount : Integer = 2;
 }
part entry_338cf74c19a5d376 {
 attribute entryKey : String = "delegated-matrix";
 attribute category : String = "raw";
 attribute caseCount : Integer = 160;
 attribute expectedAllow : Integer = 2;
 attribute expectedDeny : Integer = 158;
 attribute revisionCount : Integer = 2;
 }
part entry_10d6e8603c6c7751 {
 attribute entryKey : String = "department-synthesis-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 22;
 attribute expectedAllow : Integer = 14;
 attribute expectedDeny : Integer = 8;
 attribute revisionCount : Integer = 5;
 }
part entry_f2de460910e12475 {
 attribute entryKey : String = "expense-governance-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 27;
 attribute expectedAllow : Integer = 14;
 attribute expectedDeny : Integer = 13;
 attribute revisionCount : Integer = 9;
 }
part entry_a4dbc8562dfabe19 {
 attribute entryKey : String = "extension-coverage";
 attribute category : String = "raw";
 attribute caseCount : Integer = 8;
 attribute expectedAllow : Integer = 5;
 attribute expectedDeny : Integer = 3;
 attribute revisionCount : Integer = 4;
 }
part entry_653648fb62e9781a {
 attribute entryKey : String = "lakehouse-gateway-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 16;
 attribute expectedAllow : Integer = 6;
 attribute expectedDeny : Integer = 10;
 attribute revisionCount : Integer = 4;
 }
part entry_9e4671ad1f07e9d8 {
 attribute entryKey : String = "mission-successor";
 attribute category : String = "raw";
 attribute caseCount : Integer = 68;
 attribute expectedAllow : Integer = 34;
 attribute expectedDeny : Integer = 34;
 attribute revisionCount : Integer = 6;
 }
part entry_08a5d55aa920f2a1 {
 attribute entryKey : String = "model-stewardship";
 attribute category : String = "raw";
 attribute caseCount : Integer = 22;
 attribute expectedAllow : Integer = 6;
 attribute expectedDeny : Integer = 16;
 attribute revisionCount : Integer = 3;
 }
part entry_bd6980d0f21b4631 {
 attribute entryKey : String = "multi-account-banking-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 41;
 attribute expectedAllow : Integer = 37;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 4;
 }
part entry_1dcfbc624c37f595 {
 attribute entryKey : String = "my-health-record-consumer-platform";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 26;
 attribute expectedAllow : Integer = 8;
 attribute expectedDeny : Integer = 18;
 attribute revisionCount : Integer = 4;
 }
part entry_3583855493f99cef {
 attribute entryKey : String = "namespaced-enum-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 4;
 attribute expectedAllow : Integer = 3;
 attribute expectedDeny : Integer = 1;
 attribute revisionCount : Integer = 2;
 }
part entry_3009be769fb8f956 {
 attribute entryKey : String = "network";
 attribute category : String = "raw";
 attribute caseCount : Integer = 9;
 attribute expectedAllow : Integer = 3;
 attribute expectedDeny : Integer = 6;
 attribute revisionCount : Integer = 2;
 }
part entry_136f0db083021342 {
 attribute entryKey : String = "network-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 9;
 attribute expectedAllow : Integer = 3;
 attribute expectedDeny : Integer = 6;
 attribute revisionCount : Integer = 2;
 }
part entry_b6d7e470c6239cf0 {
 attribute entryKey : String = "payment-release";
 attribute category : String = "raw";
 attribute caseCount : Integer = 28;
 attribute expectedAllow : Integer = 15;
 attribute expectedDeny : Integer = 13;
 attribute revisionCount : Integer = 6;
 }
part entry_09f9dfeb26215c24 {
 attribute entryKey : String = "prior-authorization-internal-channels";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 22;
 attribute expectedAllow : Integer = 11;
 attribute expectedDeny : Integer = 11;
 attribute revisionCount : Integer = 9;
 }
part entry_1a322d4ce9b27187 {
 attribute entryKey : String = "prior-authorization-malformed";
 attribute category : String = "raw";
 attribute caseCount : Integer = 1;
 attribute expectedAllow : Integer = 0;
 attribute expectedDeny : Integer = 1;
 attribute revisionCount : Integer = 1;
 }
part entry_97a790112a598c11 {
 attribute entryKey : String = "prior-authorization-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 45;
 attribute expectedAllow : Integer = 31;
 attribute expectedDeny : Integer = 14;
 attribute revisionCount : Integer = 5;
 }
part entry_da7c8e55a5363756 {
 attribute entryKey : String = "pseudonymization-deployable";
 attribute category : String = "artifacts";
 attribute caseCount : Integer = 0;
 attribute expectedAllow : Integer = 0;
 attribute expectedDeny : Integer = 0;
 attribute revisionCount : Integer = 0;
 }
part entry_8d442d48dbc9fb18 {
 attribute entryKey : String = "pseudonymization-tabular";
 attribute category : String = "data";
 attribute caseCount : Integer = 0;
 attribute expectedAllow : Integer = 0;
 attribute expectedDeny : Integer = 0;
 attribute revisionCount : Integer = 0;
 }
part entry_3108500c54c3bc79 {
 attribute entryKey : String = "pseudonymization-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 41;
 attribute expectedAllow : Integer = 15;
 attribute expectedDeny : Integer = 26;
 attribute revisionCount : Integer = 7;
 }
part entry_ec92b2af9194f356 {
 attribute entryKey : String = "purchase-approval";
 attribute category : String = "raw";
 attribute caseCount : Integer = 9;
 attribute expectedAllow : Integer = 4;
 attribute expectedDeny : Integer = 5;
 attribute revisionCount : Integer = 4;
 }
part entry_a67d8ebe0260af12 {
 attribute entryKey : String = "reconciliation-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 32;
 attribute expectedAllow : Integer = 25;
 attribute expectedDeny : Integer = 7;
 attribute revisionCount : Integer = 7;
 }
part entry_fdcc28de06c94d2c {
 attribute entryKey : String = "scope-pattern";
 attribute category : String = "raw";
 attribute caseCount : Integer = 5;
 attribute expectedAllow : Integer = 3;
 attribute expectedDeny : Integer = 2;
 attribute revisionCount : Integer = 2;
 }
part entry_03f27b959e51ab77 {
 attribute entryKey : String = "scope-pattern-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 5;
 attribute expectedAllow : Integer = 3;
 attribute expectedDeny : Integer = 2;
 attribute revisionCount : Integer = 2;
 }
part entry_04affa1d5b9d7a75 {
 attribute entryKey : String = "shared-budget";
 attribute category : String = "raw";
 attribute caseCount : Integer = 35;
 attribute expectedAllow : Integer = 18;
 attribute expectedDeny : Integer = 17;
 attribute revisionCount : Integer = 6;
 }
part entry_b673fbc824107cce {
 attribute entryKey : String = "source-custody-validated";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 40;
 attribute expectedAllow : Integer = 16;
 attribute expectedDeny : Integer = 24;
 attribute revisionCount : Integer = 5;
 }
part entry_36d8e3b522d811b8 {
 attribute entryKey : String = "supplier-transition";
 attribute category : String = "raw";
 attribute caseCount : Integer = 26;
 attribute expectedAllow : Integer = 11;
 attribute expectedDeny : Integer = 15;
 attribute revisionCount : Integer = 5;
 }
part entry_c8d9e14c27663175 {
 attribute entryKey : String = "tenant-device";
 attribute category : String = "raw";
 attribute caseCount : Integer = 15;
 attribute expectedAllow : Integer = 11;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 5;
 }
part entry_762e23519c70843c {
 attribute entryKey : String = "ticket-sharing";
 attribute category : String = "raw";
 attribute caseCount : Integer = 9;
 attribute expectedAllow : Integer = 5;
 attribute expectedDeny : Integer = 4;
 attribute revisionCount : Integer = 4;
 }
part entry_cc858fef4721dd2c {
 attribute entryKey : String = "united-states-payer-exchange";
 attribute category : String = "schema-bound";
 attribute caseCount : Integer = 22;
 attribute expectedAllow : Integer = 6;
 attribute expectedDeny : Integer = 16;
 attribute revisionCount : Integer = 4;
 }
part entry_391238be70933cb3 {
 attribute entryKey : String = "vla-command";
 attribute category : String = "raw";
 attribute caseCount : Integer = 15;
 attribute expectedAllow : Integer = 8;
 attribute expectedDeny : Integer = 7;
 attribute revisionCount : Integer = 6;
 }
part entry_8a13753d54a92453 {
 attribute entryKey : String = "wearable-triage";
 attribute category : String = "raw";
 attribute caseCount : Integer = 26;
 attribute expectedAllow : Integer = 14;
 attribute expectedDeny : Integer = 12;
 attribute revisionCount : Integer = 4;
 }
 }
 view overview {expose group0; expose group1; expose group2; expose group3; expose group4;}
}