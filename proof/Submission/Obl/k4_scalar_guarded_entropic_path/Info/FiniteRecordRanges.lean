import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewReadouts

/-! Finite range certificates conditioned on the actual future original
world, in the form used by the measured information-window argument. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open PathGeometry PathGeometry.PathMeasures PathGeometry.PathNodes TrueLiftChains
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Conditional finite ambiguity of a natural-valued record. -/
def FiniteRangeGiven {Ω β : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (record : Ω → ℕ) (condition : Ω → β) (budget : ℕ) : Prop :=
  ∀ j : β, ∃ U : Finset ℕ, U.card ≤ budget ∧
    ∀ᵐ z ∂P, condition z = j → record z ∈ U

/-- Reading a function of the conditioning label only enlarges its
classes, so any range valid there is also valid for the original label. -/
theorem FiniteRangeGiven.of_condition_map {Ω β γ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {record : Ω → ℕ} {condition : Ω → γ} {refined : Ω → β}
    {budget : ℕ} (h : FiniteRangeGiven P record condition budget) (f : β → γ)
    (hf : ∀ᵐ z ∂P, condition z = f (refined z)) :
    FiniteRangeGiven P record refined budget := by
  intro j
  obtain ⟨U, hU, hcover⟩ := h (f j)
  refine ⟨U, hU, ?_⟩
  filter_upwards [hf, hcover] with z he hc hz
  apply hc
  rw [he, hz]

theorem FiniteRangeGiven.congr_record {Ω β : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {record record' : Ω → ℕ} {condition : Ω → β} {budget : ℕ}
    (h : FiniteRangeGiven P record condition budget) (heq : record =ᵐ[P] record') :
    FiniteRangeGiven P record' condition budget := by
  intro j
  obtain ⟨U, hU, hcover⟩ := h j
  refine ⟨U, hU, ?_⟩
  filter_upwards [heq, hcover] with z he hc hz
  rw [← he]
  exact hc hz

/-- The local-history range of a candidate is the exact range given the
future actual original-world label. This is the conditioning in hs. -/
theorem finiteRangeGiven_viewAt_future
    {ctx : CriticalContext} {source : MaximizingFamily ctx} {start : ℝ} {targets : List ℝ}
    {root : Code} (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k t : ℕ)
    (P : Measure (Fin (W (path.forget.finalFamily.problem i) k) × State))
    (record : (Fin (W (path.forget.finalFamily.problem i) k) × State) → ℕ) (budget : ℕ)
    (h : FiniteRangeGiven P record
      (fun z => (path.viewAt i certs hl before n).suffixChain.history k t z.1) budget) :
    FiniteRangeGiven P record
      (fun z => (path.viewAt i certs hl before (n + t)).suffixChain.world k z.1) budget := by
  apply h.of_condition_map Fin.val
  exact Filter.Eventually.of_forall fun z =>
    path.viewAt_local_history_eq_future_world i certs hl before n k t z.1

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
