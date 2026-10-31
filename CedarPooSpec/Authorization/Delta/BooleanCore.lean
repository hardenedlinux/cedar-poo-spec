import CedarPooSpec.Authorization.Delta.OperationalExactProof

/-!
A Boolean no-gain tautology for well-formed Cedar symbolic terms. This module
uses only the interpretation theorems; it does not compute a policy revision or
trust a solver answer.
-/

namespace CedarPooSpec.Authorization.Delta.BooleanCore

open Cedar.SymCC

/-- New allow paths may add a trusted-device guard to either changed path;
    each is contained in the corresponding old allow path. -/
def formula (pb pa ra rb st td : Term) : Term :=
  let base := Factory.and pb (Factory.and ra st)
  let newBob := Factory.and pb (Factory.and rb (Factory.and st td))
  let newAlice := Factory.and pa (Factory.and ra (Factory.and st td))
  let oldBob := Factory.and pb (Factory.and rb st)
  let oldAlice := Factory.and pa (Factory.and ra st)
  Factory.and (Factory.or base (Factory.or newBob newAlice))
    (Factory.not (Factory.or base (Factory.or oldBob oldAlice)))

private theorem booleanCore (pb pa ra rb st td : Bool) :
    ((((pb && ra && st) || (pb && rb && st && td) || (pa && ra && st && td)) &&
      !((pb && ra && st) || (pb && rb && st) || (pa && ra && st)))) = false := by
  cases pb <;> cases pa <;> cases ra <;> cases rb <;> cases st <;> cases td <;> decide

private structure BoolEval (εs : SymEntities) (I : Interpretation) (t : Term) (b : Bool) where
  wf : t.WellFormed εs
  ty : t.typeOf = .bool
  interp : t.interpret I = (b : Term)

private theorem atomEval {εs : SymEntities} {I : Interpretation} {t : Term}
    (hI : I.WellFormed εs) (h : t.WellFormed εs ∧ t.typeOf = .bool) :
    ∃ b, BoolEval εs I t b := by
  have hLit := Cedar.Thm.interpret_term_wfl hI h.1
  obtain ⟨b, hb⟩ := Cedar.Thm.wfl_of_type_bool_is_bool hLit.1 (hLit.2.trans h.2)
  exact ⟨b, h.1, h.2, hb⟩

private theorem andEval {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (hI : I.WellFormed εs) (h₁ : BoolEval εs I t₁ b₁) (h₂ : BoolEval εs I t₂ b₂) :
    BoolEval εs I (Factory.and t₁ t₂) (b₁ && b₂) := by
  have hw := Cedar.Thm.wf_and h₁.wf h₂.wf h₁.ty h₂.ty
  refine ⟨hw.1, hw.2, ?_⟩
  rw [Cedar.Thm.interpret_and hI h₁.wf h₂.wf h₁.ty h₂.ty, h₁.interp, h₂.interp]
  cases b₁ <;> cases b₂ <;> rfl

private theorem orEval {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (hI : I.WellFormed εs) (h₁ : BoolEval εs I t₁ b₁) (h₂ : BoolEval εs I t₂ b₂) :
    BoolEval εs I (Factory.or t₁ t₂) (b₁ || b₂) := by
  have hw := Cedar.Thm.wf_or h₁.wf h₂.wf h₁.ty h₂.ty
  refine ⟨hw.1, hw.2, ?_⟩
  rw [Cedar.Thm.interpret_or hI h₁.wf h₂.wf h₁.ty h₂.ty, h₁.interp, h₂.interp]
  cases b₁ <;> cases b₂ <;> rfl

private theorem notEval {εs : SymEntities} {I : Interpretation} {t : Term} {b : Bool}
    (hI : I.WellFormed εs) (h : BoolEval εs I t b) :
    BoolEval εs I (Factory.not t) (!b) := by
  have hw := Cedar.Thm.wf_not h.wf h.ty
  refine ⟨hw.1, hw.2, ?_⟩
  rw [Cedar.Thm.interpret_not hI h.wf, h.interp]
  cases b <;> rfl

/-- The expansion formula is false in every well-formed interpretation of
    six well-formed Boolean terms. -/
theorem formulaFalse {εs : SymEntities} (I : Interpretation) (hI : I.WellFormed εs)
    (pb pa ra rb st td : Term)
    (hpb : pb.WellFormed εs ∧ pb.typeOf = .bool)
    (hpa : pa.WellFormed εs ∧ pa.typeOf = .bool)
    (hra : ra.WellFormed εs ∧ ra.typeOf = .bool)
    (hrb : rb.WellFormed εs ∧ rb.typeOf = .bool)
    (hst : st.WellFormed εs ∧ st.typeOf = .bool)
    (htd : td.WellFormed εs ∧ td.typeOf = .bool) :
    (formula pb pa ra rb st td).interpret I = (false : Term) := by
  obtain ⟨bpb, epb⟩ := atomEval hI hpb
  obtain ⟨bpa, epa⟩ := atomEval hI hpa
  obtain ⟨bra, era⟩ := atomEval hI hra
  obtain ⟨brb, erb⟩ := atomEval hI hrb
  obtain ⟨bst, est⟩ := atomEval hI hst
  obtain ⟨btd, etd⟩ := atomEval hI htd
  have ebase := andEval hI epb (andEval hI era est)
  have enewBob := andEval hI epb (andEval hI erb (andEval hI est etd))
  have enewAlice := andEval hI epa (andEval hI era (andEval hI est etd))
  have eoldBob := andEval hI epb (andEval hI erb est)
  have eoldAlice := andEval hI epa (andEval hI era est)
  have eformula := andEval hI
    (orEval hI ebase (orEval hI enewBob enewAlice))
    (notEval hI (orEval hI ebase (orEval hI eoldBob eoldAlice)))
  have hBool :
      (((bpb && (bra && bst)) ||
        ((bpb && (brb && (bst && btd))) ||
         (bpa && (bra && (bst && btd))))) &&
      !((bpb && (bra && bst)) ||
        ((bpb && (brb && bst)) || (bpa && (bra && bst))))) = false := by
    simpa only [Bool.and_assoc, Bool.or_assoc] using
      booleanCore bpb bpa bra brb bst btd
  simpa only [formula, hBool] using eformula.interp

/-- Kernel-checked logical core: query shape and atom well-formedness remain
    explicit premises, independent of any fixture computation. -/
theorem unsatOfShapeAndWellFormedAtoms
    (εnv : SymEnv) (asserts : Asserts) (pb pa ra rb st td : Term)
    (hShape : asserts = [(true : Term), formula pb pa ra rb st td])
    (hpb : pb.WellFormed εnv.entities ∧ pb.typeOf = .bool)
    (hpa : pa.WellFormed εnv.entities ∧ pa.typeOf = .bool)
    (hra : ra.WellFormed εnv.entities ∧ ra.typeOf = .bool)
    (hrb : rb.WellFormed εnv.entities ∧ rb.typeOf = .bool)
    (hst : st.WellFormed εnv.entities ∧ st.typeOf = .bool)
    (htd : td.WellFormed εnv.entities ∧ td.typeOf = .bool) :
    εnv ⊭ asserts := by
  rw [Cedar.Thm.asserts_unsatisfiable_def]
  intro I hI
  refine ⟨formula pb pa ra rb st td, ?_, ?_⟩
  · rw [hShape]
    simp
  · rw [formulaFalse I hI pb pa ra rb st td hpb hpa hra hrb hst htd]
    decide

end CedarPooSpec.Authorization.Delta.BooleanCore
