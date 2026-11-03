// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: expense-exposure
permit(
  principal is AnyCompany::User,
  action in [AnyCompany::Action::"listTeamExpenses",AnyCompany::Action::"rejectExpense"],
  resource is AnyCompany::Expense
);

// POO policy ID: reject-department-boundary
forbid(
  principal is AnyCompany::User,
  action == AnyCompany::Action::"rejectExpense",
  resource is AnyCompany::Expense
) when {
  !(principal.department == resource.department)
};

// POO policy ID: reject-duty-boundary
forbid(
  principal is AnyCompany::User,
  action == AnyCompany::Action::"rejectExpense",
  resource is AnyCompany::Expense
) when {
  principal.email == resource.submitterEmail
};

// POO policy ID: reject-role-boundary
forbid(
  principal is AnyCompany::User,
  action == AnyCompany::Action::"rejectExpense",
  resource is AnyCompany::Expense
) when {
  !(principal in AnyCompany::Group::"ExpenseApprovers")
};

// POO policy ID: reject-state-boundary
forbid(
  principal is AnyCompany::User,
  action == AnyCompany::Action::"rejectExpense",
  resource is AnyCompany::Expense
) when {
  !(resource.status == "submitted")
};

// POO policy ID: team-row-boundary
forbid(
  principal is AnyCompany::User,
  action == AnyCompany::Action::"listTeamExpenses",
  resource is AnyCompany::Expense
) when {
  !(principal.department == resource.department)
};
