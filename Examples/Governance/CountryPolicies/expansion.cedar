// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: europe-member-approval
permit(
  principal in Role::"Approver-Europe",
  action in [Action::"approve",Action::"review"],
  resource in TimesheetGrp::"European-timesheets"
);

// POO policy ID: france
permit(
  principal in Role::"Approver-France",
  action in [Action::"ApproverActions"],
  resource in TimesheetGrp::"French-timesheets"
);

// POO policy ID: germany
permit(
  principal in Role::"Approver-Germany",
  action in [Action::"ApproverActions"],
  resource in TimesheetGrp::"German-timesheets"
);

// POO policy ID: japan
permit(
  principal in Role::"Approver-Japan",
  action in [Action::"ApproverActions"],
  resource in TimesheetGrp::"Japanese-timesheets"
);

// POO policy ID: uk
permit(
  principal in Role::"Approver-UK",
  action in [Action::"ApproverActions"],
  resource in TimesheetGrp::"UK-timesheets"
);
