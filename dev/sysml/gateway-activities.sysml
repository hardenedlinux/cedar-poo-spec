// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

package GatewayProfileFlow {
 private import Views::*; private import ScalarValues::*;
 part def Definition;
 part stepSession : Definition;
 attribute stepSessionSymbol : String = "CedarPooSpec.Gateway.ProfileObject.openSession";
 attribute stepSessionSource : String = "CedarPooSpec/Gateway/ProfileObject.lean";
 part stepCapture : Definition;
 attribute stepCaptureSymbol : String = "CedarPooSpec.Gateway.ProfileObject.capturePublication";
 attribute stepCaptureSource : String = "CedarPooSpec/Gateway/ProfileAdmission.lean";
 part stepAuthorize : Definition;
 attribute stepAuthorizeSymbol : String = "CedarPooSpec.Gateway.authorize";
 attribute stepAuthorizeSource : String = "CedarPooSpec/Gateway/Admission.lean";
 part stepBind : Definition;
 attribute stepBindSymbol : String = "CedarPooSpec.Gateway.bindPublication";
 attribute stepBindSource : String = "CedarPooSpec/Gateway/ProfileAdmission.lean";
 part stepAccepted : Definition;
 attribute stepAcceptedSymbol : String = "CedarPooSpec.Gateway.PublishedReceipt";
 attribute stepAcceptedSource : String = "CedarPooSpec/Gateway/ProfileAdmission.lean";
 part stepRefused : Definition;
 attribute stepRefusedSymbol : String = "CedarPooSpec.Gateway.Error";
 attribute stepRefusedSource : String = "CedarPooSpec/Gateway/Admission.lean";
 connection edge0 connect stepSession to stepCapture;
 connection edge1 connect stepSession to stepRefused;
 connection edge2 connect stepCapture to stepAuthorize;
 connection edge3 connect stepCapture to stepRefused;
 connection edge4 connect stepAuthorize to stepBind;
 connection edge5 connect stepAuthorize to stepRefused;
 connection edge6 connect stepBind to stepAccepted;
 connection edge7 connect stepBind to stepRefused;
 view overview {
  expose stepSession; expose stepCapture; expose stepAuthorize; expose stepBind; expose stepAccepted; expose stepRefused;
  expose edge0; expose edge1; expose edge2; expose edge3; expose edge4; expose edge5; expose edge6; expose edge7;
  render asInterconnectionDiagram;
 }
}

// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

package GatewayPublicationLanes {
 private import Views::*; private import ScalarValues::*;
 part def Definition;
 part stepCapture : Definition;
 part stepCall : Definition;
 part stepCheck : Definition;
 part stepAdmit : Definition;
 part stepInstall : Definition;
 part stepObserve : Definition;
 part stepReturn : Definition;
 connection edge0 connect stepCapture to stepCall;
 connection edge1 connect stepCall to stepCheck;
 connection edge2 connect stepCheck to stepAdmit;
 connection edge3 connect stepAdmit to stepInstall;
 connection edge4 connect stepInstall to stepObserve;
 connection edge5 connect stepObserve to stepReturn;
 view overview {
  expose stepCapture; expose stepCall; expose stepCheck; expose stepAdmit; expose stepInstall; expose stepObserve; expose stepReturn;
  expose edge0; expose edge1; expose edge2; expose edge3; expose edge4; expose edge5;
  render asInterconnectionDiagram;
 }
}

// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0

package GatewayFinalTasks {
 attribute completeStructure : String = "GatewayFinalTasks::stepFinal";
 private import Views::*; private import ScalarValues::*;
 part def Definition;
 part stepFinal : Definition;
 attribute stepFinalSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final";
 attribute stepFinalSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepReceipt : Definition;
 attribute stepReceiptSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.receipt";
 attribute stepReceiptSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepApproved : Definition;
 attribute stepApprovedSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.approved";
 attribute stepApprovedSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepDurable : Definition;
 attribute stepDurableSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.durable";
 attribute stepDurableSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepRecovered : Definition;
 attribute stepRecoveredSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.recovered";
 attribute stepRecoveredSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepFenced : Definition;
 attribute stepFencedSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.fenced";
 attribute stepFencedSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepCurrent : Definition;
 attribute stepCurrentSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.current";
 attribute stepCurrentSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepPending : Definition;
 attribute stepPendingSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.pending";
 attribute stepPendingSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 part stepCommitted : Definition;
 attribute stepCommittedSymbol : String = "CedarPooSpec.Gateway.PublicationReview.Final.committed";
 attribute stepCommittedSource : String = "CedarPooSpec/Gateway/PublicationReview.lean";
 connection edge0 connect stepFinal to stepReceipt;
 connection edge1 connect stepFinal to stepApproved;
 connection edge2 connect stepFinal to stepDurable;
 connection edge3 connect stepFinal to stepRecovered;
 connection edge4 connect stepFinal to stepFenced;
 connection edge5 connect stepFinal to stepCurrent;
 connection edge6 connect stepFinal to stepPending;
 connection edge7 connect stepFinal to stepCommitted;
 view overview {
  expose stepFinal; expose stepReceipt; expose stepApproved; expose stepDurable; expose stepRecovered; expose stepFenced; expose stepCurrent; expose stepPending; expose stepCommitted;
  expose edge0; expose edge1; expose edge2; expose edge3; expose edge4; expose edge5; expose edge6; expose edge7;
  render asInterconnectionDiagram;
 }
}
