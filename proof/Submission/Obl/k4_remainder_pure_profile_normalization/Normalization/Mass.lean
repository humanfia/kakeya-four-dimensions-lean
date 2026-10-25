/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/Normalization/Mass.lean.
Earlier provenance is preserved below.
-/
/-
Adapted from this LOT tree, o064, session x0214, commit 1213d02,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/Mass.lean.
Earlier provenance is preserved below.
-/
import Mathlib

/-!
# Selected mass under normalization

The selected incidence mass of a lifted packet equals the parent time length
times the mass of the child packet for the pushed-forward assigned prior: paper
(2.13) `m_cd = q ν_c m'_d` before the division by `ν_c`.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

open MeasureTheory

/-- Lebesgue measure under the affine time change `t ↦ (t - t₀) / q`, `q > 0`. -/
theorem map_volume_affine (t₀ q : ℝ) (hq : 0 < q) :
    Measure.map (fun t : ℝ => (t - t₀) / q) volume = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun s => q⁻¹ * s) ∘ (fun t => t + -t₀) := by
    funext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const _),
    map_add_right_eq_self, Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv,
    abs_of_pos hq]

/-- The product mass of a lifted incidence set. -/
theorem prod_lift_apply {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (Φ : α → α) (hΦ : Measurable Φ) (A : Set α) (hA : MeasurableSet A) (t₀ q : ℝ) (hq : 0 < q)
    (F' : Set (α × ℝ)) (hF' : MeasurableSet F') :
    (ν.prod volume) {p | p.1 ∈ A ∧ (Φ p.1, (p.2 - t₀) / q) ∈ F'} =
      ENNReal.ofReal q * ((Measure.map Φ (ν.restrict A)).prod volume) F' := by
  have hG : Measurable (Prod.map Φ (fun t : ℝ => (t - t₀) / q)) :=
    hΦ.prodMap ((measurable_sub_const _).div_const _)
  have hset : {p : α × ℝ | p.1 ∈ A ∧ (Φ p.1, (p.2 - t₀) / q) ∈ F'} =
      (Prod.map Φ (fun t : ℝ => (t - t₀) / q)) ⁻¹' F' ∩ (A ×ˢ Set.univ) := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Prod.map,
      Set.mem_prod, Set.mem_univ, and_true]; tauto
  rw [hset, ← Measure.restrict_apply' (hA.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ, ← Measure.map_apply hG hF',
    ← Measure.map_prod_map _ _ hΦ ((measurable_sub_const _).div_const _),
    map_volume_affine t₀ q hq, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul]

end Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
