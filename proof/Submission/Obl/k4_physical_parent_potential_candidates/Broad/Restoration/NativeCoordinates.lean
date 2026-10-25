-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/NativeCoordinates.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/NativeCoordinates.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineTransport
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

/-!
# The native equation of a group in normalized coordinates

The group test is the old native quadratic `R0` minus the potential `Pot` (with its common
intercept), in physical coordinates. A normalization `coordinateMap c M B` (affine on the base,
the hidden coordinate scaled by the world's `B`) with an explicit inverse `(c', M', B')`
transports them to `S0 = transportPolynomial c' M' B' R0` and `P0 = basePullback c' M' Pot`.
In normalized coordinates the group equation `S0 - P0 = 0` is the native quadratic equation
`a w² + nativeB(z) w + nativeC(z) = 0` with `a = curvature S0 / 2`; its hidden derivative is
`2 a w + nativeB(z)`. These are the identities `hSeq`, `hSd` of the sampled packaging.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization Submission.Obl.k4_stable_native_signal_oscillation

lemma vec_eq_snoc (z : Base) (w : ℝ) :
    (![z 0, z 1, z 2, w] : Fin 4 → ℝ) = Fin.snoc (fun i : Fin 3 => z i) w := by
  funext i
  fin_cases i <;> rfl

/-- The affine base substitution `z ↦ c' + M' z`. -/
def baseSubstitution (c' : Fin 3 → ℝ) (M' : Matrix (Fin 3) (Fin 3) ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun k => C (c' k) + ∑ j : Fin 3, C (M' k j) * X j

/-- The pullback of a base polynomial under `z ↦ c' + M' z`. -/
def basePullback (c' : Fin 3 → ℝ) (M' : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  bind₁ (baseSubstitution c' M') P

lemma eval_basePullback (c' : Fin 3 → ℝ) (M' : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    eval z (basePullback c' M' P) = eval (fun k => c' k + ∑ j : Fin 3, M' k j * z j) P := by
  change eval₂Hom (RingHom.id ℝ) z (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 3 → ℝ => eval₂Hom (RingHom.id ℝ) f P)
  funext k
  simp [baseSubstitution]

lemma totalDegree_basePullback (c' : Fin 3 → ℝ) (M' : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 3) ℝ) : (basePullback c' M' P).totalDegree ≤ P.totalDegree := by
  apply Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine
  intro k
  have hmul (a : ℝ) (j : Fin 3) : (C a * X j : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  apply (totalDegree_add _ _).trans
  exact max_le (by simp) (totalDegree_finsetSum_le fun j _ => hmul _ _)

/-- The hidden-quadratic coefficient of the native equation. -/
def nativeA (S : Poly) : ℝ := curvature S (3 : Fin 4) / 2

/-- The hidden-linear coefficient of the native equation. -/
def nativeB (S : Poly) : MvPolynomial (Fin 3) ℝ := restrictBase (pderiv (3 : Fin 4) S)

/-- The constant coefficient of the native equation of the group test `S - P`. -/
def nativeC (S : Poly) (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  restrictBase S - P

lemma totalDegree_nativeB (S : Poly) (hS : S.totalDegree ≤ 2) : (nativeB S).totalDegree ≤ 1 :=
  (totalDegree_restrictBase _).trans (by
    have := Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le S (3 : Fin 4)
    omega)

lemma totalDegree_nativeC (S : Poly) (P : MvPolynomial (Fin 3) ℝ) {d : ℕ}
    (hS : S.totalDegree ≤ 2) (h2 : 2 ≤ d) (hP : P.totalDegree ≤ d) :
    (nativeC S P).totalDegree ≤ d :=
  (totalDegree_sub _ _).trans (max_le ((totalDegree_restrictBase S).trans (hS.trans h2)) hP)

lemma fin_three_eq_last : (3 : Fin 4) = Fin.last 3 := rfl

/-- The group equation in normalized coordinates is the native quadratic equation. -/
theorem native_equation (S : Poly) (hS : S.totalDegree ≤ 2) (P : MvPolynomial (Fin 3) ℝ)
    (z : Base) (w : ℝ) :
    eval ![z 0, z 1, z 2, w] S - eval (fun i => z i) P =
      nativeA S * w ^ 2 + eval (fun i => z i) (nativeB S) * w +
        eval (fun i => z i) (nativeC S P) := by
  rw [vec_eq_snoc]
  have h := eval_snoc_quadratic S hS (fun i : Fin 3 => z i) w
  rw [h]
  simp only [nativeA, nativeB, nativeC, eval_sub, fin_three_eq_last]
  ring

/-- Its hidden derivative. -/
theorem native_derivative (S : Poly) (hS : S.totalDegree ≤ 2) (z : Base) (w : ℝ) :
    eval ![z 0, z 1, z 2, w] (pderiv (3 : Fin 4) S) =
      2 * nativeA S * w + eval (fun i => z i) (nativeB S) := by
  simp only [nativeA, nativeB, fin_three_eq_last]
  have hdeg : (pderiv (Fin.last 3) S).totalDegree ≤ 2 :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le S (Fin.last 3)).trans
      (by omega)
  rw [vec_eq_snoc]
  have h := eval_snoc_quadratic (pderiv (Fin.last 3) S) hdeg (fun i : Fin 3 => z i) w
  have hsecond : pderiv (Fin.last 3) (pderiv (Fin.last 3) S) = C (curvature S (Fin.last 3)) :=
    second_pderiv_eq_curvature S hS (Fin.last 3)
  have hthird : curvature (pderiv (Fin.last 3) S) (Fin.last 3) = 0 := by
    rw [curvature, hsecond]
    simp
  rw [h, hsecond, hthird]
  simp only [eval_restrictBase, eval_C, zero_mul, zero_div, add_zero]
  ring

lemma coordinateMap_castSucc (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ)
    (x : Fin 4 → ℝ) (j : Fin 3) :
    coordinateMap c M B x j.castSucc = c j + ∑ l : Fin 3, M j l * x l.castSucc := by
  fin_cases j <;> rfl

lemma coordinateMap_hidden (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ)
    (x : Fin 4 → ℝ) : coordinateMap c M B x (Fin.last 3) = B * x (Fin.last 3) := rfl

/-- An explicit inverse of a normalization. -/
theorem coordinateMap_inverse {c c' : Fin 3 → ℝ} {M M' : Matrix (Fin 3) (Fin 3) ℝ} {B B' : ℝ}
    (hM : M' * M = 1) (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j) (hB : B' * B = 1)
    (x : Fin 4 → ℝ) : coordinateMap c' M' B' (coordinateMap c M B x) = x := by
  have hMe : ∀ k l, ∑ j : Fin 3, M' k j * M j l = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hM k) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hbase : ∀ k : Fin 3, c' k + ∑ j : Fin 3, M' k j *
      (c j + ∑ l : Fin 3, M j l * x l.castSucc) = x k.castSucc := by
    intro k
    rw [hc k]
    have hsum : ∑ j : Fin 3, M' k j * (c j + ∑ l : Fin 3, M j l * x l.castSucc) =
        ∑ j : Fin 3, M' k j * c j + ∑ l : Fin 3, (∑ j : Fin 3, M' k j * M j l) * x l.castSucc := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    simp only [hMe, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [coordinateMap_hidden, coordinateMap_hidden, ← mul_assoc, hB, one_mul]
  | cast k =>
    rw [coordinateMap_castSucc]
    simp_rw [coordinateMap_castSucc]
    exact hbase k

/-- The transported native quadratic evaluates at normalized points as the physical one. -/
theorem eval_normalized_native {c c' : Fin 3 → ℝ} {M M' : Matrix (Fin 3) (Fin 3) ℝ}
    {B B' : ℝ} (hM : M' * M = 1) (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j)
    (hB : B' * B = 1) (R0 : Poly) (x : Fin 4 → ℝ) :
    eval (coordinateMap c M B x) (transportPolynomial c' M' B' R0) = eval x R0 ∧
    eval (coordinateMap c M B x) (pderiv (3 : Fin 4) (transportPolynomial c' M' B' R0)) =
      B' * eval x (pderiv (3 : Fin 4) R0) := by
  have hinv := coordinateMap_inverse hM hc hB x
  refine ⟨?_, ?_⟩
  · rw [eval_transportPolynomial, hinv]
  · rw [(eval_transport_hidden_derivatives c' M' B' R0 _).1, hinv]

/-- The pulled-back potential evaluates at normalized base points as the physical one. -/
theorem eval_normalized_potential {c c' : Fin 3 → ℝ} {M M' : Matrix (Fin 3) (Fin 3) ℝ}
    {B B' : ℝ} (hM : M' * M = 1) (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j)
    (hB : B' * B = 1) (Pot : MvPolynomial (Fin 3) ℝ) (x : Fin 4 → ℝ) :
    eval (fun i : Fin 3 => coordinateMap c M B x i.castSucc) (basePullback c' M' Pot) =
      eval (fun i : Fin 3 => x i.castSucc) Pot := by
  rw [eval_basePullback]
  have hinv := coordinateMap_inverse hM hc hB x
  apply congrArg (fun v : Fin 3 → ℝ => eval v Pot)
  funext k
  have hk := congrFun hinv k.castSucc
  rw [coordinateMap_castSucc] at hk
  simp_rw [coordinateMap_castSucc] at hk
  exact hk

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
