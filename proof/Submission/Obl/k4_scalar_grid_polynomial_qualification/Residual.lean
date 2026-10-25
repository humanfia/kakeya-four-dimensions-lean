import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory Filter

/-- A nonnegative sequence tends to zero if it has no cofinal sequence on which
it stays a fixed positive distance above zero. -/
theorem tendsto_zero_of_no_dense_subsequence (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (h : ∀ δ : ℝ, 0 < δ → ∀ φ : ℕ → ℕ,
      Tendsto φ atTop atTop → (∀ k, δ ≤ a (φ k)) → False) :
    Tendsto a atTop (nhds 0) := by
  refine tendsto_order.2 ⟨fun c hc => .of_forall (fun k => hc.trans_le (ha k)), ?_⟩
  intro δ hδ
  by_contra hh
  have hfreq : ∃ᶠ k in atTop, δ ≤ a k :=
    (Filter.not_eventually.mp hh).mono fun k hk => le_of_not_gt hk
  obtain ⟨φ, hφ, hφa⟩ := Filter.subseq_forall_of_frequently
    (x := id) (p := fun k => δ ≤ a k) tendsto_id hfreq
  exact h δ hδ φ hφ hφa

/-- The discovery criterion only has to return positive mass inside a
substantial residual. All measures and all labels remain the original ones. -/
theorem vanishing_failure_ratio_of_residual_discovery
    {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (μ : (k : ℕ) → Measure (α k)) (B Q : (k : ℕ) → Set (α k))
    (hdisj : ∀ k, Disjoint (B k) (Q k))
    (hdiscover : ∀ δ : ℝ, 0 < δ → ∀ φ : ℕ → ℕ,
      Tendsto φ atTop atTop →
      (∀ k, δ ≤ (μ (φ k) (B (φ k))).toReal / (μ (φ k) univ).toReal) →
      ∃ k, 0 < μ (φ k) (B (φ k) ∩ Q (φ k))) :
    Tendsto (fun k => (μ k (B k)).toReal / (μ k univ).toReal) atTop (nhds 0) := by
  apply tendsto_zero_of_no_dense_subsequence
    _ (fun k => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  intro δ hδ φ hφ hφB
  obtain ⟨k, hk⟩ := hdiscover δ hδ φ hφ hφB
  rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj (φ k)), measure_empty] at hk
  exact (lt_irrefl 0) hk

/-- A measurable failure superset is sufficient for the frozen outer-measure
failure ratio, so exact existential fits need not themselves be Borel. -/
theorem vanishing_failure_ratio_of_superset
    {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (μ : (k : ℕ) → Measure (α k)) (B B' : (k : ℕ) → Set (α k))
    (hμ : ∀ k, μ k univ ≠ ⊤) (hBB' : ∀ k, B k ⊆ B' k)
    (hlim : Tendsto (fun k => (μ k (B' k)).toReal / (μ k univ).toReal)
      atTop (nhds 0)) :
    Tendsto (fun k => (μ k (B k)).toReal / (μ k univ).toReal) atTop (nhds 0) := by
  refine squeeze_zero
    (fun k => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun k => ?_) hlim
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono
    (ne_top_of_le_ne_top (hμ k) (measure_mono (subset_univ (B' k))))
    (measure_mono (hBB' k))

end Submission.Obl.k4_scalar_grid_polynomial_qualification
