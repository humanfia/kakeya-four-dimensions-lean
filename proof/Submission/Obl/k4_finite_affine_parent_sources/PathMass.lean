-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Path
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal
import Submission.Obl.k4_true_forest_own_depth_preparation.IncidenceBudget
import Submission.Obl.k4_true_forest_own_depth_preparation.ForestPruning

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open scoped Classical

noncomputable section

/-- The full original assignment in its actual old time block. -/
def PathData.packet {W : ℕ} (p : PathData W) (b : Fin p.C) : Set Incidence :=
  p.assigned b ×ˢ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
    (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

lemma PathData.Valid.counted_measurable (b : Fin p.C) : MeasurableSet (p.counted b) :=
  (hp.chart b).2.2.2.2.2.2.2.1

lemma PathData.Valid.assigned_measurable (b : Fin p.C) : MeasurableSet (p.assigned b) :=
  (hp.chart b).2.2.2.2.2.2.1

/-- The complete terminal path has the unchanged original mass floor. -/
lemma PathData.Valid.terminal_mass_lower (hm : 0 < m) :
    ENNReal.ofReal p.κ⁻¹ ≤ ∑ w, ENNReal.ofReal (ω w) *
      (ν w).prod volume (TerminalInc W p.C m p.lev p.world p.counted w) := by
  classical
  have hmass := Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask_mass ν
    (fun w => ENNReal.ofReal (ω w)) (m - 1) (p.T (m - 1))
    p.lev p.world p.bin p.assigned p.counted
    (fun b _ => hp.counted_measurable b)
    (fun b hb z hz => by
      have hs := hp.counted_support b z hz
      simpa only [hb] using And.intro hs.2.1 hs.2.2.1)
    (fun b b' hb hb' hne hw hj =>
      hp.assignment_disjoint b b' hne (hb.trans hb'.symm) hw hj)
  apply (hp.level_bounds (m - 1) (by omega)).2.2.2.2.2.trans
  rw [← hmass]
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_right
  apply measure_mono
  exact Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask_subset _ _ _ _ _ _ w

/-- A half-mass residual is still inverse-slack substantial on the ORIGINAL
world priors. No conditional reference law is used here. -/
lemma PathData.Valid.residual_mass_lower (hm : 0 < m)
    (H : Fin W → Set Incidence)
    (hH : (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω w) *
        (ν w).prod volume (TerminalInc W p.C m p.lev p.world p.counted w)) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w)) :
    ENNReal.ofReal ((2 * p.κ)⁻¹) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.one_le_slack
  have h := mul_le_mul_right (hp.terminal_mass_lower hm) (1 / 2 : ENNReal)
  apply (le_of_eq ?_).trans (h.trans hH)
  rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  field_simp

/-- Full assignments across one original layer consume at most one
world-weighted unit of trajectory-times-uniform-time mass. -/
lemma PathData.Valid.assignment_time_budget
    (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω₀ : ∀ w, 0 ≤ ω w) (hω : ∑ w, ω w = 1) (i : ℕ) :
    (∑ b, if p.lev b = i then ENNReal.ofReal (ω (p.world b)) *
      (ν (p.world b)).prod volume (p.packet b) else 0) ≤ 1 := by
  classical
  let I := {b : Fin p.C // p.lev b = i}
  let bin : I → Fin (2 ^ p.T i) := fun b =>
    ⟨p.bin b.val, by simpa only [b.property] using hp.label_bin b.val⟩
  have hb := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    ν ω (fun b : I => p.world b.val) bin (fun b => p.assigned b.val) hν hω₀ hω
    (fun b => hp.assigned_measurable b.val)
    (fun b b' hne hw hj => hp.assignment_disjoint b.val b'.val
      (fun h => hne (Subtype.ext h)) (b.property.trans b'.property.symm) hw
      (congrArg Fin.val hj))
  simp only [Fintype.card_fin] at hb
  have hprod (b : I) : (ν (p.world b.val)).prod volume (p.packet b.val) =
      ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.world b.val) (p.assigned b.val) := by
    let := hν (p.world b.val)
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc, b.property]
    rw [show ((p.bin b.val : ℝ) + 1) / (2 : ℝ) ^ p.T i -
      (p.bin b.val : ℝ) / (2 : ℝ) ^ p.T i = ((2 : ℝ) ^ p.T i)⁻¹ by ring]
    exact mul_comm _ _
  have hsum : (∑ b, if p.lev b = i then ENNReal.ofReal (ω (p.world b)) *
      (ν (p.world b)).prod volume (p.packet b) else 0) =
      ∑ b : I, ENNReal.ofReal (ω (p.world b.val)) *
        (ν (p.world b.val)).prod volume (p.packet b.val) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hsum]
  simp_rw [hprod, mul_left_comm (ENNReal.ofReal (ω _))]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_right hb _).trans_eq
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have heq : ((2 : ℝ) ^ p.T i)⁻¹ * ((2 ^ p.T i : ℕ) : ℝ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ (by positivity)
  rw [heq, ENNReal.ofReal_one]

/-- The accepted forest pruning estimate applies directly to the supplied
positive path, with its literal original counted masses and world weights. -/
lemma PathData.Valid.removed_descendant_mass_le
    (good : Fin p.C → Prop) (i : ℕ) :
    (∑ b, if p.lev b = i ∧
        ¬Submission.Obl.k4_true_forest_own_depth_preparation.Kept p.lev p.par good b then
      ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (p.counted b) else 0) ≤
      ∑ b, if ¬good b then ENNReal.ofReal (ω (p.world b)) *
        (ν (p.world b)).prod volume (p.counted b) else 0 := by
  classical
  apply Submission.Obl.k4_true_forest_own_depth_preparation.forest_removed_mass_le
    p.lev p.par _ good (fun b hb => (hp.parent b hb).1)
  intro a
  apply Submission.Obl.k4_true_forest_own_depth_preparation.forest_child_budget
    ν (fun w => ENNReal.ofReal (ω w)) p.T p.lev p.par p.world p.bin
    p.assigned p.counted (fun b => hp.counted_measurable b)
    (fun b b' hne hl hw hj => hp.assignment_disjoint b b' hne hl hw hj)
    (fun b z hz => ⟨(hp.counted_support b z hz).2.1, (hp.counted_support b z hz).2.2.1⟩)
    (fun b hb => ⟨(hp.parent b hb).1, (hp.parent b hb).2.1, (hp.parent b hb).2.2.2.1⟩)

end

end

end Submission.Obl.k4_finite_affine_parent_sources
