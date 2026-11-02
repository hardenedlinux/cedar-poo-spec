import CedarPooSpec.Governance.Veto

/-! A reusable source change owner for release composition. The Host must
authenticate repository history, review, status checks, identities and current
ruleset state before projecting the claim. -/

namespace CedarPooSpec.Cloud.Pipeline

open Cedar.Spec CedarPooSpec.Governance

structure SourceControlBoundary where
  policyId : PolicyID
  actionScope : ActionScope
  resourceScope : ResourceScope
  protectedBranch : String
  principalScope : PrincipalScope := .principalScope .any
  deriving DecidableEq

private def fact (name : String) : Expr := .getAttr (.var .context) name
private def target (name : String) : Expr := .getAttr (.var .resource) name
private def change (name : String) : Expr :=
  .getAttr (fact "sourceChange") name
private def same (left right : Expr) : Expr := .binaryApp .eq left right
private def no (condition : Expr) : Expr := .unaryApp .not condition
private def all (conditions : List Expr) : Expr :=
  conditions.foldr Expr.and (.lit (.bool true))

/-- The reviewed commit and current branch-rule epoch must describe the
    selected artifact's source. A distinct reviewer, checks, and an enforced
    protected branch are required for this default profile. -/
def SourceControlBoundary.ready (boundary : SourceControlBoundary) : Expr :=
  all [fact "sourceChangeVerified", fact "sourceIdentityVerified",
    same (change "repository") (target "sourceRepository"),
    same (change "commit") (target "sourceCommit"),
    same (change "branch") (.lit (.string boundary.protectedBranch)),
    same (change "policyEpoch") (fact "currentSourceEpoch"),
    no (same (change "author") (change "reviewer")),
    change "reviewApproved", change "reviewerHuman", change "checksPassed",
    change "branchProtected", no (change "bypassUsed"),
    no (change "historyRewritten")]

def SourceControlBoundary.veto (boundary : SourceControlBoundary) : Veto :=
  { policyId := boundary.policyId
    actionScope := boundary.actionScope
    resourceScope := boundary.resourceScope
    principalScope := boundary.principalScope
    denyWhen := no boundary.ready }

end CedarPooSpec.Cloud.Pipeline
