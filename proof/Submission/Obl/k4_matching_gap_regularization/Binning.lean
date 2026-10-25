import Submission.Obl.k4_matching_gap_regularization.Bins
import Submission.Obl.k4_matching_gap_regularization.Restriction

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open MeasureTheory Set
open scoped ENNReal

/-- Simultaneous gap binning, retaining an identically zero exponent in a
designated coordinate and recording the exact conditioning loss. -/
lemma regularize_gaps {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : ι → α → ℝ)
    (hg : ∀ j, Measurable (g j)) (P : ι → Prop)
    {m : ℕ} (hm : 0 < m) {N : ℝ} (hN : 1 ≤ N)
    (hgap : ∀ᵐ p ∂μ, (∀ j, g j p ≤ N ^ (1 / (m : ℝ))) ∧
      ∃ j, P j ∧ N ^ (-(1 / (m : ℝ))) ≤ g j p) :
    ∃ (β : ι → ℝ) (ν : Measure α),
      (∀ j, 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j, P j ∧ β j = 0) ∧
      IsProbabilityMeasure ν ∧
      (∀ E : Set α, ν E ≤ ((2 * m + 1) ^ Fintype.card ι : ℝ≥0∞) * μ E) ∧
      (∀ᵐ p ∂ν, ∀ j, Band N (1 / (m : ℝ)) (β j) (g j p)) := by
  classical
  let S : (ι → Fin (2 * m + 1)) → Set α := fun b =>
    {p | (∃ j, P j ∧ b j = 0) ∧ ∀ j, Band N (1 / (m : ℝ)) (binExponent m (b j)) (g j p)}
  have hS : ∀ b, MeasurableSet (S b) := by
    intro b
    dsimp [S, Band]
    measurability
  have hcover : ∀ᵐ p ∂μ, ∃ b, p ∈ S b := by
    filter_upwards [hgap] with p hp
    choose b hb hforce using fun j => exists_bin hm hN (hp.1 j)
    refine ⟨b, ?_, hb⟩
    obtain ⟨j, hj, hlarge⟩ := hp.2
    exact ⟨j, hj, hforce j hlarge⟩
  obtain ⟨b, ν, hprob, hbound, hnull⟩ := finite_cover_restriction μ S hS hcover
  letI : IsProbabilityMeasure ν := hprob
  have hmem : ∀ᵐ p ∂ν, p ∈ S b := (ae_iff).2 hnull
  obtain ⟨p, hp⟩ := hmem.exists
  refine ⟨fun j => binExponent m (b j), ν, fun j => binExponent_mem hm (b j), ?_,
    hprob, ?_, hmem.mono fun p hp => hp.2⟩
  · obtain ⟨j, hj, hjzero⟩ := hp.1
    exact ⟨j, hj, by simp [hjzero, binExponent]⟩
  · simpa [Fintype.card_fun] using hbound

end Submission.Obl.k4_matching_gap_regularization
