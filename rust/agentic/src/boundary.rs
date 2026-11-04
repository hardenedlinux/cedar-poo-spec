//! Reusable tool-effect boundary mirrored from the Lean AgenticAI library.
//! A caller must authenticate observed tool state and the final sink audience.

use std::collections::HashSet;

/// Before and after candidate sets visible to a sink after a selection tool call.
#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SelectionDelta {
    pub before: Vec<String>,
    pub after: Vec<String>,
}

impl SelectionDelta {
    pub fn well_formed(&self) -> bool {
        let before: HashSet<_> = self.before.iter().collect();
        let after: HashSet<_> = self.after.iter().collect();
        !self.before.is_empty()
            && !self.after.is_empty()
            && before.len() == self.before.len()
            && after.len() == self.after.len()
            && self.after.len() < self.before.len()
            && after.is_subset(&before)
    }
}

/// Typed action category resolved from the tool operation outside model text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ToolAction {
    ContentWrite,
    SelectionMutation,
}

/// Typed destination category resolved from the actual endpoint and ACL.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SinkClass {
    SharedWorkspace,
    DirectMessage,
    RemoteModel,
}

/// Host-observed facts used for action and sink checks on one effect.
pub struct BoundaryFacts<'a> {
    pub action: ToolAction,
    pub sink: SinkClass,
    pub intended_selection: Option<&'a SelectionDelta>,
    pub observed_selection: Option<&'a SelectionDelta>,
    pub candidate_ids: &'a [String],
    pub output_bound: bool,
    pub audience_allowed: bool,
    pub remote_model_approved: bool,
}

/// Every applicable action and sink check must pass. No caller-supplied name
/// can select a weaker method, and a missing observation fails closed.
pub fn admitted(facts: &BoundaryFacts<'_>) -> bool {
    if !facts.output_bound || !facts.audience_allowed {
        return false;
    }
    let action_allowed = match facts.action {
        ToolAction::ContentWrite => {
            facts.intended_selection.is_none() && facts.observed_selection.is_none()
        }
        ToolAction::SelectionMutation => match facts.intended_selection {
            Some(delta) => {
                facts.observed_selection == Some(delta)
                    && delta.well_formed()
                    && facts.candidate_ids == delta.after
            }
            None => false,
        },
    };
    action_allowed
        && match facts.sink {
            SinkClass::SharedWorkspace | SinkClass::DirectMessage => true,
            SinkClass::RemoteModel => facts.remote_model_approved,
        }
}

#[cfg(test)]
#[path = "../tests/unit/agentic_ai_boundary.rs"]
mod tests;
