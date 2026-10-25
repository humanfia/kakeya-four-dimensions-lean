-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedReferenceBudget.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedSourceDomains
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.EligibleReferenceBudget
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CoarserNativeCaps

/-! Original reference total of actual eligible true and projected domain families. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open CommonDomain

noncomputable section

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

theorem reference_bound (hp : p.Valid) (hcommon : a.Common p)
    (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) {aTable : ℝ} (haTable : 0 < aTable)
    (n₁ n₂ : Fin D.n → ℕ)
    (trueIdx : ∀ u, Fin (n₁ u) → Fin (a.n k s) × Bool)
    (projectedIdx : ∀ u, Fin (n₂ u) → Fin L.n)
    (htrue : ∀ u, Function.Injective (trueIdx u))
    (hprojected : ∀ u, Function.Injective (projectedIdx u))
    (heligible₁ : ∀ u i, D.decode u ∈ D.trueMenus (trueIdx u i).1)
    (heligible₂ : ∀ u j, D.decode u ∈ D.projectedMenus (projectedIdx u j)) :
    (∑ u, ((n₁ u : ℝ) * ((q * χ * m) * aTable ^ p.d *
        (a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode u) 1}).toReal) +
      (n₂ u : ℝ) * ((q * χ * m) * aTable ^ p.d *
        (a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode u) 1}).toReal))) ≤
      (aTable / PreparedModel.width p k s) ^ p.d *
        (475200 * p.K k ^ 5 + 360 * H ^ 4 * p.K k) := by
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hwidth : 0 < PreparedModel.width p k s := Real.rpow_pos_of_pos hN _
  have hK : 0 ≤ p.K k := zero_le_one.trans (hp.2.2.1.1 k)
  let factor := (aTable / PreparedModel.width p k s) ^ p.d
  have hfactor : 0 ≤ factor := Real.rpow_nonneg (by positivity) _
  let oldWeight (c : Code) := q * χ * m * (PreparedModel.width p k s) ^ p.d *
    (a.pi k {w : ℝ | ⌊w / χ⌋ = c 1}).toReal
  let newWeight (c : Code) := q * χ * m * aTable ^ p.d *
    (a.pi k {w : ℝ | ⌊w / χ⌋ = c 1}).toReal
  have hscale (c : Code) : newWeight c = factor * oldWeight c := by
    dsimp only [newWeight, oldWeight, factor]
    rw [fine_reference_scale hwidth haTable.le]
    ring
  have hsum (menus : Finset Code) : (∑ c ∈ menus, newWeight c) =
      factor * ∑ c ∈ menus, oldWeight c := by
    simp only [hscale, Finset.mul_sum]
  have hsum' {n : ℕ} (menus : Fin n → Finset Code) :
      (∑ i, ∑ c ∈ menus i, newWeight c) = factor * ∑ i, ∑ c ∈ menus i, oldWeight c := by
    simp only [hsum, Finset.mul_sum]
  have hT : (∑ i, ∑ c ∈ D.trueMenus i, newWeight c) ≤ factor * (237600 * p.K k ^ 5) := by
    rw [hsum']
    exact mul_le_mul_of_nonneg_left D.true_reference hfactor
  have hρ : (a.rho k univ).toReal ≤ p.K k := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (a.rho_univ_le p hcommon k)
    simpa only [ENNReal.toReal_ofReal hK] using h
  have hP : (∑ i, ∑ c ∈ D.projectedMenus i, newWeight c) ≤ factor * (360 * H ^ 4 * p.K k) := by
    rw [hsum']
    apply mul_le_mul_of_nonneg_left _ hfactor
    exact D.projected_reference.trans (mul_le_mul_of_nonneg_left hρ (by positivity))
  have h := eligible_original_reference_budget D.decode D.injective_decode
    D.trueMenus D.projectedMenus n₁ n₂ trueIdx projectedIdx htrue hprojected
    heligible₁ heligible₂ newWeight (fun c => by dsimp [newWeight]; positivity)
  calc
    _ ≤ 2 * (∑ i, ∑ c ∈ D.trueMenus i, newWeight c) +
        ∑ i, ∑ c ∈ D.projectedMenus i, newWeight c := h
    _ ≤ 2 * (factor * (237600 * p.K k ^ 5)) + factor * (360 * H ^ 4 * p.K k) :=
      add_le_add (mul_le_mul_of_nonneg_left hT (by norm_num)) hP
    _ = _ := by dsimp only [factor]; ring

end PreparedDomainData

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
