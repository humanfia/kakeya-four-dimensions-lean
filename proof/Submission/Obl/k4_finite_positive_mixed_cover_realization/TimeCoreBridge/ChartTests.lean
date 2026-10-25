-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/ChartTests.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/ChartTests.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ChartTests.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Tests
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RepTests

/-!
# The improved chart test of a label and its three-point trajectory set

`labelTest low B lam P` is the normalized test `B λ P` (low curvature) or the affine-centre
test `(B / qc P) ∂_w P` (high curvature). `testSet` keeps the lines on which it satisfies the
value and derivative bounds at the endpoints and the midpoint of a block; this set has a fixed
Boolean format, and on it the whole-block tests hold (`testSet_whole`). A line whose hidden
coordinate stays within `η̃ / B` of a normalized branch of `P` on the block lies in `testSet`
(`mem_testSet_of_close`).
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The chart test of a representative. -/
noncomputable def labelTest (low : Bool) (B lam : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  if low then C (B * lam) * P else C (B / qc P) * pderiv 3 P

theorem totalDegree_labelTest_le {low : Bool} {B lam : ℝ} {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) : (labelTest low B lam P).totalDegree ≤ 2 := by
  unfold labelTest
  cases low
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pderiv_le' P (3 : Fin 4) (d := 1) hP).trans (by norm_num)
  · simp only [↓reduceIte]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hP

theorem coeff_C_mul_abs (a : ℝ) (P : MvPolynomial (Fin 4) ℝ) (e : Fin 4 →₀ ℕ) :
    |(C a * P).coeff e| = |a| * |P.coeff e| := by
  rw [coeff_C_mul, abs_mul]

theorem coeff_pderiv_abs_le {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {H : ℝ}
    (hH : ∀ e, |P.coeff e| ≤ H) (e : Fin 4 →₀ ℕ) : |(pderiv 3 P).coeff e| ≤ 3 * H := by
  rw [coeff_pderiv, abs_mul]
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  by_cases hc : P.coeff (e + Finsupp.single 3 1) = 0
  · rw [hc, abs_zero, zero_mul]; positivity
  · have hdeg := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
    have he3 : e 3 + 1 ≤ 2 := by
      have hsum : (e + Finsupp.single 3 1).sum (fun _ k => k) =
          e.sum (fun _ k => k) + 1 := by
        rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
        simp
      have h3 : e 3 ≤ e.sum (fun _ k => k) := by
        classical
        by_cases h : e 3 = 0
        · rw [h]; exact Nat.zero_le _
        · exact Finset.single_le_sum (f := fun i => e i) (fun _ _ => Nat.zero_le _)
            (Finsupp.mem_support_iff.mpr h)
      omega
    have : |((e 3 : ℕ) + 1 : ℝ)| ≤ 3 := by
      rw [abs_of_nonneg (by positivity)]
      have : ((e 3 : ℕ) : ℝ) + 1 ≤ 2 := by exact_mod_cast he3
      linarith
    calc |P.coeff (e + Finsupp.single 3 1)| * |((e 3 : ℕ) : ℝ) + 1|
        ≤ H * 3 := mul_le_mul (hH _) this (abs_nonneg _) hH0
      _ = 3 * H := by ring

/-- The three-point trajectory set of a test on a block `[ta, tb]`. -/
def testSet (R₂ : MvPolynomial (Fin 4) ℝ) (ta tb m₀ m₁ : ℝ) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | |eval (gx l ta) R₂| ≤ m₀ ∧ |eval (gx l ((ta + tb) / 2)) R₂| ≤ m₀ ∧
    |eval (gx l tb) R₂| ≤ m₀ ∧ |eval (gx l ta) (pderiv 3 R₂)| ≤ m₁ ∧
    |eval (gx l tb) (pderiv 3 R₂)| ≤ m₁}

theorem testSet_whole {R₂ : MvPolynomial (Fin 4) ℝ} (hR : R₂.totalDegree ≤ 2) {ta tb m₀ m₁ : ℝ}
    (hab : ta < tb) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ testSet R₂ ta tb m₀ m₁) :
    ∀ t ∈ Set.Icc ta tb, |eval (gx l t) R₂| ≤ 3 * m₀ ∧ |eval (gx l t) (pderiv 3 R₂)| ≤ m₁ :=
  whole_block_of_three_points hR l hab hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2

/-- The slice of the three-point set at a copy index has a fixed Boolean format. -/
theorem gfmt_testSet {R₂ : MvPolynomial (Fin 4) ℝ} (hR : R₂.totalDegree ≤ 2) {ta tb m₀ m₁ : ℝ}
    (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁) (i : ℕ) :
    gfmt 6 5 4 {x | (i, x) ∈ testSet R₂ ta tb m₀ m₁} := by
  have hd1 : (pderiv (3 : Fin 4) R₂).totalDegree ≤ 2 :=
    (totalDegree_pderiv_le' R₂ (3 : Fin 4) (d := 1) hR).trans (by norm_num)
  have hs : ∀ (t : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (m : ℝ), 0 ≤ m → Q.totalDegree ≤ 2 →
      gfmt 6 1 4 {x : Fin 6 → ℝ | |eval (gx (i, x) t) Q| ≤ m} := by
    intro t Q m hm hQ
    have h := gfmt_abs_le (slicePoly t Q) hm
    have hdeg : 2 * (slicePoly t Q).totalDegree ≤ 4 := by
      have := totalDegree_slicePoly_le t Q
      omega
    have hset : {x : Fin 6 → ℝ | |eval x (slicePoly t Q)| ≤ m} =
        {x : Fin 6 → ℝ | |eval (gx (i, x) t) Q| ≤ m} := by
      ext x
      simp only [Set.mem_ofPred_eq, eval_slicePoly t Q i x]
    rw [← hset]
    exact gfmt_mono le_rfl hdeg h
  have e : {x | (i, x) ∈ testSet R₂ ta tb m₀ m₁} =
      {x : Fin 6 → ℝ | |eval (gx (i, x) ta) R₂| ≤ m₀} ∩
        ({x : Fin 6 → ℝ | |eval (gx (i, x) ((ta + tb) / 2)) R₂| ≤ m₀} ∩
          ({x : Fin 6 → ℝ | |eval (gx (i, x) tb) R₂| ≤ m₀} ∩
            ({x : Fin 6 → ℝ | |eval (gx (i, x) ta) (pderiv 3 R₂)| ≤ m₁} ∩
              {x : Fin 6 → ℝ | |eval (gx (i, x) tb) (pderiv 3 R₂)| ≤ m₁}))) := by
    ext x
    simp [testSet]
  rw [e]
  have h := gfmt_inter (hs ta R₂ m₀ hm₀ hR) (gfmt_inter (hs ((ta + tb) / 2) R₂ m₀ hm₀ hR)
    (gfmt_inter (hs tb R₂ m₀ hm₀ hR) (gfmt_inter (hs ta _ m₁ hm₁ hd1) (hs tb _ m₁ hm₁ hd1))))
  refine gfmt_mono (by norm_num) (by simp) h

/-- Closeness to a normalized branch puts a line into the three-point set of its label test,
and gives the derivative lower bound at every time of the block. -/
theorem labelTest_bounds {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {low : Bool}
    {lam ηt B : ℝ} (hlam : 0 < lam) (hηt : 0 < ηt) (hB : 0 < B)
    (hlow : low = true → |qc P| * (ηt / B) ≤ lam⁻¹ / 4)
    (hhigh : low = false → lam⁻¹ / 4 < |qc P| * (ηt / B))
    {x : Fin 4 → ℝ} {f : ℝ} (hroot : eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) P = 0)
    (hder₁ : 1 / 2 ≤ lam * |eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) (pderiv 3 P)|)
    (hder₂ : lam * |eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) (pderiv 3 P)| ≤ 2)
    (hclose : |x 3 - f| ≤ ηt / B) :
    |eval x (labelTest low B lam P)| ≤ 9 * ηt ∧
      B / 4 ≤ |eval x (pderiv 3 (labelTest low B lam P))| ∧
      |eval x (pderiv 3 (labelTest low B lam P))| ≤ 9 * B / 4 ∧
      |eval x (pderiv 3 (pderiv 3 (labelTest low B lam P)))| ≤ B ^ 2 / (4 * ηt) := by
  have hη : 0 < ηt / B := div_pos hηt hB
  have hBη : B * (ηt / B) = ηt := by field_simp
  cases low
  · have h := rep_high hP hlam hη hB (hhigh rfl) hder₂ hclose
    simp only [labelTest, Bool.false_eq_true, ↓reduceIte]
    rw [hBη] at h
    refine ⟨by linarith [h.1], ?_, ?_, ?_⟩
    · rw [h.2.1, abs_of_pos hB]; linarith
    · rw [h.2.1, abs_of_pos hB]; linarith
    · rw [h.2.2, abs_zero]; positivity
  · have h := rep_low hP hlam hB hη (hlow rfl) hroot hder₁ hder₂ hclose
    simp only [labelTest, ↓reduceIte]
    rw [hBη] at h
    refine ⟨by linarith [h.1], h.2.1, h.2.2.1, ?_⟩
    have : B / (4 * (ηt / B)) = B ^ 2 / (4 * ηt) := by field_simp
    rw [← this]
    exact h.2.2.2

/-- The curvature of a label test is constant and bounded through its curvature type. -/
theorem labelTest_curv {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {low : Bool}
    {lam ηt B : ℝ} (hlam : 0 < lam) (hηt : 0 < ηt) (hB : 0 < B)
    (hlow : low = true → |qc P| * (ηt / B) ≤ lam⁻¹ / 4) (x : Fin 4 → ℝ) :
    |eval x (pderiv 3 (pderiv 3 (labelTest low B lam P)))| ≤ B ^ 2 / (4 * ηt) := by
  cases low
  · simp only [labelTest, Bool.false_eq_true, ↓reduceIte]
    have h1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
    have h0 : (pderiv (3 : Fin 4) (pderiv 3 P)).totalDegree ≤ 0 := totalDegree_pderiv_le' _ _ h1
    have h3 : pderiv (3 : Fin 4) (pderiv 3 (pderiv 3 P)) = 0 := by
      rw [eq_C_of_totalDegree_eq_zero _ (Nat.le_zero.mp h0), pderiv_C]
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero, h3, map_zero,
      abs_zero]
    positivity
  · simp only [labelTest, ↓reduceIte]
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero, map_mul, eval_C]
    have hq : eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) = qc P :=
      eval_pderiv2_eq_qc (n := 3) P hP x
    rw [hq, abs_mul, abs_of_pos (by positivity : 0 < B * lam)]
    have h := hlow rfl
    rw [le_div_iff₀ (by positivity)]
    have e : B * lam * |qc P| * (4 * ηt) = 4 * B ^ 2 * lam * (|qc P| * (ηt / B)) := by
      field_simp
    rw [e]
    have : 4 * B ^ 2 * lam * (|qc P| * (ηt / B)) ≤ 4 * B ^ 2 * lam * (lam⁻¹ / 4) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    calc _ ≤ 4 * B ^ 2 * lam * (lam⁻¹ / 4) := this
      _ = B ^ 2 := by field_simp

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
