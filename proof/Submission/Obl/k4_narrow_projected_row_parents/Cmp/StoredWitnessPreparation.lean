/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/StoredWitnessPreparation.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_horizontal_coefficient_count.Selection

/-! Common floor pruning with measurable indices into the unchanged original witnesses. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A surviving disjoint subfamily decodes the original assignment measurably.
The original index and the stored witness are unchanged almost everywhere. -/
theorem reindex_assigned_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : μ univ ≠ 0) {n n' : ℕ}
    (W : Fin n → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
    (old : Ω → Fin n) (hold : Measurable old)
    (hassigned : ∀ᵐ p ∂μ, p ∈ W (old p))
    (idx : Fin n' → Fin n) (hinj : Function.Injective idx)
    (hcover : ∀ᵐ p ∂μ, ∃ j, p ∈ W (idx j)) :
    ∃ current : Ω → Fin n', Measurable current ∧
      ∀ᵐ p ∂μ, idx (current p) = old p ∧ p ∈ W (idx (current p)) := by
  classical
  obtain ⟨p₀, -, j₀, -⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμ
    (by simpa using hcover : ∀ᵐ p ∂μ.restrict univ, ∃ j, p ∈ W (idx j))
  letI : Nonempty (Fin n') := ⟨j₀⟩
  let inv : Fin n → Fin n' := Function.invFun idx
  have hleft : Function.LeftInverse inv idx := Function.leftInverse_invFun hinj
  refine ⟨inv ∘ old, (measurable_of_finite inv).comp hold, ?_⟩
  filter_upwards [hassigned, hcover] with p hp hpc
  obtain ⟨j, hj⟩ := hpc
  have heq : old p = idx j := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hp hj
  change idx (inv (old p)) = old p ∧ p ∈ W (idx (inv (old p)))
  rw [heq, hleft j]
  exact ⟨rfl, hj⟩

/-- Apply the accepted simultaneous floor pruning to all colors of one domain at once,
then retain their actual measurable original assignment indices. Every floor is
also a floor under the original law, for use after later comparison deletions. -/
theorem prepare_original_witness_families {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} (n : Fin m → ℕ)
    (W : (r : Fin m) → Fin (n r) → Set Ω)
    (hW : ∀ r i, MeasurableSet (W r i))
    (hdisj : ∀ r, Pairwise (fun i j => Disjoint (W r i) (W r j)))
    (old : (r : Fin m) → Ω → Fin (n r)) (hold : ∀ r, Measurable (old r))
    (hassigned : ∀ r, ∀ᵐ p ∂μ, p ∈ W r (old r p))
    (w : (r : Fin m) → Fin (n r) → ℝ≥0∞) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ r, ∑ i, w r i ∧
      (ρ univ = 0 ∨ ∃ (n' : Fin m → ℕ)
        (idx : (r : Fin m) → Fin (n' r) → Fin (n r))
        (current : (r : Fin m) → Ω → Fin (n' r)),
        (∀ r, Function.Injective (idx r)) ∧ (∀ r, n' r ≤ n r) ∧
        (∀ r, Measurable (current r)) ∧
        (∀ r i, w r (idx r i) ≤ ρ (W r (idx r i))) ∧
        (∀ r i, w r (idx r i) ≤ μ (W r (idx r i))) ∧
        ∀ r, ∀ᵐ p ∂ρ, idx r (current r p) = old r p ∧
          p ∈ W r (idx r (current r p))) := by
  classical
  have hcover (r : Fin m) : μ {p | ∃ i, p ∈ W r i}ᶜ = 0 :=
    ae_iff.mp ((hassigned r).mono fun p hp => ⟨old r p, hp⟩)
  obtain ⟨ρ, hρ, hloss, n', idx, hinj, hfloor, hcover'⟩ :=
    Submission.Obl.k4_horizontal_coefficient_count.finite_floor_subfamilies μ n W hW w hcover
  refine ⟨ρ, hρ, hloss, ?_⟩
  by_cases hzero : ρ univ = 0
  · exact Or.inl hzero
  · right
    have hidx (r : Fin m) := reindex_assigned_family ρ hzero (W r) (hdisj r)
      (old r) (hold r) ((hassigned r).filter_mono (ae_mono hρ))
      (idx r) (hinj r) (ae_iff.mpr (hcover' r))
    choose current hmeas hcurrent using hidx
    exact ⟨n', idx, current, hinj,
      (fun r => by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (idx r) (hinj r)),
      hmeas, hfloor, (fun r i => (hfloor r i).trans (hρ _)), hcurrent⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
