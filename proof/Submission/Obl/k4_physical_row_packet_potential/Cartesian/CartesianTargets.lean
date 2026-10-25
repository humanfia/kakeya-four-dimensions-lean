-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CartesianTargets.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CartesianTargets.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/CartesianTargets.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CartesianGrids
import Submission.Lib.K4DeterminantBreadth

/-!
Separate Cartesian anchor coordinates from target coordinates. Dense
finite grids yield one good anchor array with many complete targets.
Every mixed anchor/target vertex is explicitly included in the test.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian

noncomputable section

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Y] [Fintype Z] in
theorem mean_tuple_snoc (p : X → ℝ) (k : ℕ) (F : (Fin (k + 1) → X) → ℝ) :
    mean (tupleWeight p) F =
      mean (tupleWeight p) (fun xs : Fin k → X => mean p (fun x => F (Fin.snoc xs x))) := by
  classical
  rw [mean, Submission.Lib.K4DeterminantBreadth.sum_snoc k]
  simp only [tupleWeight, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem gridDensity3_snoc (p : X → ℝ) (q : Y → ℝ) (r : Z → ℝ)
    (f : X → Y → Z → ℝ) (k : ℕ) :
    gridDensity3 p q r f (k + 1) =
      mean (tupleWeight p) (fun xs : Fin k → X =>
        mean (tupleWeight q) (fun ys : Fin k → Y =>
          mean (tupleWeight r) (fun zs : Fin k → Z =>
            mean p (fun x => mean q (fun y => mean r (fun z =>
              ∏ c : Fin (k + 1), ∏ b : Fin (k + 1), ∏ a : Fin (k + 1),
                f ((Fin.snoc xs x : Fin (k + 1) → X) a) ((Fin.snoc ys y : Fin (k + 1) → Y) b) ((Fin.snoc zs z : Fin (k + 1) → Z) c))))))) := by
  unfold gridDensity3
  rw [mean_tuple_snoc]
  apply congrArg (mean (tupleWeight p))
  funext xs
  simp_rw [mean_tuple_snoc q k, mean_tuple_snoc r k]
  rw [mean_comm p (tupleWeight q)]
  apply congrArg (mean (tupleWeight q))
  funext ys
  simp_rw [mean_comm q (tupleWeight r)]
  exact mean_comm p (tupleWeight r) _

open Classical in
/-- Complete-grid success includes anchors, the target, and all mixed vertices. -/
def completeTarget (R : X → Y → Z → Prop) {k : ℕ}
    (xs : Fin k → X) (ys : Fin k → Y) (zs : Fin k → Z) (x : X) (y : Y) (z : Z) : Prop :=
  ∀ a b c : Fin (k + 1), R ((Fin.snoc xs x : Fin (k + 1) → X) a) ((Fin.snoc ys y : Fin (k + 1) → Y) b) ((Fin.snoc zs z : Fin (k + 1) → Z) c)

omit [Fintype X] [Fintype Y] [Fintype Z] in
open Classical in
theorem completeTarget_indicator (R : X → Y → Z → Prop) {k : ℕ}
    (xs : Fin k → X) (ys : Fin k → Y) (zs : Fin k → Z) (x : X) (y : Y) (z : Z) :
    (if completeTarget R xs ys zs x y z then (1 : ℝ) else 0) =
      ∏ c : Fin (k + 1), ∏ b : Fin (k + 1), ∏ a : Fin (k + 1),
        if R ((Fin.snoc xs x : Fin (k + 1) → X) a) ((Fin.snoc ys y : Fin (k + 1) → Y) b) ((Fin.snoc zs z : Fin (k + 1) → Z) c) then (1 : ℝ) else 0 := by
  by_cases h : completeTarget R xs ys zs x y z
  · simp only [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro c _
    apply Finset.prod_eq_one
    intro b _
    apply Finset.prod_eq_one
    intro a _
    exact ite_eq_left (h a b c)
  · rw [ite_eq_right h]
    symm
    have hn : ∃ a b c : Fin (k + 1),
        ¬ R ((Fin.snoc xs x : Fin (k + 1) → X) a)
          ((Fin.snoc ys y : Fin (k + 1) → Y) b)
          ((Fin.snoc zs z : Fin (k + 1) → Z) c) := by
      simpa only [completeTarget, not_forall] using h
    obtain ⟨a, b, c, habc⟩ := hn
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right habc)

open Classical in
/-- Any explicit small bad-anchor probability leaves one good array with
many complete targets. The target set retains every interpolation vertex. -/
theorem exists_good_anchors_dense_complete_targets
    (p : X → ℝ) (q : Y → ℝ) (r : Z → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (hr : ∀ z, 0 ≤ r z)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1) (hrsum : ∑ z, r z = 1)
    (R : X → Y → Z → Prop) (k : ℕ) (δ β : ℝ) (hδ : 0 ≤ δ)
    (hdensity : δ ≤ mean p (fun x => mean q (fun y => mean r
      (fun z => if R x y z then (1 : ℝ) else 0))))
    (good : (Fin k → X) × (Fin k → Y) × (Fin k → Z) → Prop)
    (hgap : β < δ ^ ((k + 1) ^ 3))
    (hbad : mean (jointWeight (tupleWeight p) (jointWeight (tupleWeight q) (tupleWeight r)))
      (fun a => if good a then (0 : ℝ) else 1) ≤ β) :
    ∃ (xs : Fin k → X) (ys : Fin k → Y) (zs : Fin k → Z), good (xs, ys, zs) ∧
      (δ ^ ((k + 1) ^ 3) - β) / 2 ≤
        mean p (fun x => mean q (fun y => mean r
          (fun z => if completeTarget R xs ys zs x y z then (1 : ℝ) else 0))) := by
  let wA : (Fin k → X) × (Fin k → Y) × (Fin k → Z) → ℝ := jointWeight (tupleWeight p) (jointWeight (tupleWeight q) (tupleWeight r))
  let wT := jointWeight p (jointWeight q r)
  let F := fun a : (Fin k → X) × (Fin k → Y) × (Fin k → Z) =>
    fun t : X × Y × Z => if completeTarget R a.1 a.2.1 a.2.2 t.1 t.2.1 t.2.2 then (1 : ℝ) else 0
  have hwA : ∀ a, 0 ≤ wA a := fun a =>
    mul_nonneg (tupleWeight_nonneg p hp _) (mul_nonneg (tupleWeight_nonneg q hq _)
      (tupleWeight_nonneg r hr _))
  have hwT : ∀ t, 0 ≤ wT t := fun t => mul_nonneg (hp _) (mul_nonneg (hq _) (hr _))
  have hsumA : ∑ a, wA a = 1 := by
    simp only [wA, sum_jointWeight, sum_tupleWeight, hpsum, hqsum, hrsum, one_pow, one_mul]
  have hsumT : ∑ t, wT t = 1 := by
    simp only [wT, sum_jointWeight, hpsum, hqsum, hrsum, one_mul]
  have hsuccess : δ ^ ((k + 1) ^ 3) ≤ mean wA (fun a => mean wT (F a)) := by
    have hpow := pow_le_pow_left₀ hδ hdensity ((k + 1) ^ 3)
    have hgrid := density_pow_cube_le_gridDensity3 p q r
      (fun x y z => if R x y z then (1 : ℝ) else 0) hp hq hr hpsum hqsum hrsum
      (by intro x y z; split_ifs <;> norm_num) (k + 1) (by omega)
    refine (hpow.trans hgrid).trans_eq ?_
    rw [gridDensity3_snoc]
    simp only [wA, wT, F, mean_jointWeight, completeTarget_indicator]
  obtain ⟨a, ha, htarget⟩ := exists_good_anchor_with_dense_targets wA wT F good
    hwA hwT hsumA hsumT (by intro a t; dsimp [F]; split_ifs <;> norm_num)
    (δ ^ ((k + 1) ^ 3)) β hgap hsuccess hbad
  exact ⟨a.1, a.2.1, a.2.2, ha, by simpa only [wT, F, mean_jointWeight] using htarget⟩

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian
