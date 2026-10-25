-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/RootTests.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/RootTests.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 6a8fa645a587,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RootTests.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.ChartTests

/-!
# Root certificates from finitely many point tests

For a quadratic test `P` (total degree at most two, hidden variable last) and a scale `s > 0`,
`rootTestSet P s m₀ ta tb` keeps the lines on which `|P| ≤ m₀` at the endpoints and the midpoint
of the block `[ta, tb]`, and `P_w` lies in `[0.9 s, 1.1 s]` (or in `[-1.1 s, -0.9 s]`) at both
endpoints. If moreover `|qc P| m₀ ≤ s² / 40`, then on the whole block every such line has a root
`w₀` of `P` over its base point within `4 m₀ / s` of its hidden coordinate, with
`s / 2 ≤ |P_w(w₀)| ≤ 2 s` (`root_certificate`). The set has a fixed Boolean format.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The derivative window at the two endpoints, with a common sign. -/
def derivWindow (P : MvPolynomial (Fin 4) ℝ) (s ta tb : ℝ) (l : ℕ × (Fin 6 → ℝ)) : Prop :=
  (9 / 10 * s ≤ eval (gx l ta) (pderiv 3 P) ∧ eval (gx l ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
    9 / 10 * s ≤ eval (gx l tb) (pderiv 3 P) ∧ eval (gx l tb) (pderiv 3 P) ≤ 11 / 10 * s) ∨
  (9 / 10 * s ≤ -eval (gx l ta) (pderiv 3 P) ∧ -eval (gx l ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
    9 / 10 * s ≤ -eval (gx l tb) (pderiv 3 P) ∧ -eval (gx l tb) (pderiv 3 P) ≤ 11 / 10 * s)

/-- The root-certificate point tests of a line on a block. -/
def rootTestSet (P : MvPolynomial (Fin 4) ℝ) (s m₀ ta tb : ℝ) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | |eval (gx l ta) P| ≤ m₀ ∧ |eval (gx l ((ta + tb) / 2)) P| ≤ m₀ ∧
    |eval (gx l tb) P| ≤ m₀ ∧ derivWindow P s ta tb l}

/-- An affine function with values in `[a, b]` at the endpoints stays in `[a, b]`. -/
theorem affine_mem_of_endpoints {c₀ c₁ t₀ t₂ a b t : ℝ}
    (h₀ : a ≤ c₀ + c₁ * t₀ ∧ c₀ + c₁ * t₀ ≤ b) (h₂ : a ≤ c₀ + c₁ * t₂ ∧ c₀ + c₁ * t₂ ≤ b)
    (ht : t ∈ Set.Icc t₀ t₂) : a ≤ c₀ + c₁ * t ∧ c₀ + c₁ * t ≤ b := by
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with h | h
  · have : t = t₀ := le_antisymm (h ▸ ht.2) ht.1
    rw [this]; exact h₀
  · set σ := (t - t₀) / (t₂ - t₀)
    have hpos : 0 < t₂ - t₀ := by linarith
    have hs0 : 0 ≤ σ := div_nonneg (by linarith [ht.1]) hpos.le
    have hs1 : σ ≤ 1 := (div_le_one hpos).mpr (by linarith [ht.2])
    have heq : c₀ + c₁ * t = (1 - σ) * (c₀ + c₁ * t₀) + σ * (c₀ + c₁ * t₂) := by
      have : t = t₀ + σ * (t₂ - t₀) := by simp only [σ]; field_simp; ring
      rw [this]; ring
    rw [heq]
    constructor <;> nlinarith

/-- Along a line, the hidden derivative of a test of degree at most two is affine in time. -/
theorem eval_pderiv_gx_affine {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) : ∃ c₀ c₁ : ℝ, ∀ t, eval (gx l t) (pderiv 3 P) = c₀ + c₁ * t := by
  have hd1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
  obtain ⟨q, hq, hqe⟩ := eval_gx_eq_poly (pderiv (3 : Fin 4) P) l
  refine ⟨q.coeff 0, q.coeff 1, fun t => ?_⟩
  rw [hqe, Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
  simp [Finset.sum_range_succ]

/-- The derivative window holds on the whole block. -/
theorem derivWindow_whole {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {s ta tb : ℝ}
    {l : ℕ × (Fin 6 → ℝ)} (hl : derivWindow P s ta tb l) {t : ℝ} (ht : t ∈ Set.Icc ta tb) :
    9 / 10 * s ≤ |eval (gx l t) (pderiv 3 P)| ∧ |eval (gx l t) (pderiv 3 P)| ≤ 11 / 10 * s ∧
      (0 ≤ eval (gx l t) (pderiv 3 P) ↔ 0 ≤ eval (gx l ta) (pderiv 3 P)) := by
  obtain ⟨c₀, c₁, hc⟩ := eval_pderiv_gx_affine hP l
  rcases hl with ⟨a1, a2, b1, b2⟩ | ⟨a1, a2, b1, b2⟩
  · rw [hc] at a1 a2 b1 b2
    have := affine_mem_of_endpoints ⟨a1, a2⟩ ⟨b1, b2⟩ ht
    rw [hc, hc]
    have hs : 0 ≤ s := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; exact this.1
    · rw [abs_of_nonneg (by linarith)]; exact this.2
    · constructor <;> intro <;> linarith
  · rw [hc] at a1 a2 b1 b2
    have := affine_mem_of_endpoints (c₀ := c₀) (c₁ := c₁) (a := -(11 / 10 * s))
      (b := -(9 / 10 * s)) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ht
    rw [hc, hc]
    have hs : 0 ≤ s := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith)]; linarith [this.2]
    · rw [abs_of_nonpos (by linarith)]; linarith [this.1]
    · constructor <;> intro h
      · by_contra; nlinarith
      · by_contra; nlinarith

/-- **Root certificate.** On a line in the root test set, with small curvature, every time of the
block has a root of the test over the base point, close to the hidden coordinate, with derivative
in `[s/2, 2s]`. -/
theorem root_certificate {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {s m₀ ta tb : ℝ}
    (hs : 0 < s) (hm₀ : 0 ≤ m₀) (hcurv : |qc P| * m₀ ≤ s ^ 2 / 40) (hab : ta < tb)
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ rootTestSet P s m₀ ta tb) {t : ℝ} (ht : t ∈ Set.Icc ta tb) :
    ∃ w₀ : ℝ, |(gx l t) 3 - w₀| ≤ 4 * m₀ / s ∧
      eval (Function.update (gx l t) (3 : Fin 4) w₀) P = 0 ∧
      s / 2 ≤ |eval (Function.update (gx l t) (3 : Fin 4) w₀) (pderiv (3 : Fin 4) P)| ∧
      |eval (Function.update (gx l t) (3 : Fin 4) w₀) (pderiv (3 : Fin 4) P)| ≤ 2 * s := by
  obtain ⟨h0, hm, h2, hwin⟩ := hl
  -- whole-block value and derivative bounds
  have hval : |eval (gx l t) P| ≤ 3 * m₀ := by
    obtain ⟨p, hp, hpe⟩ := eval_gx_eq_poly P l
    have hp2 : p.natDegree ≤ 2 := hp.trans hP
    rw [hpe] at h0 hm h2 ⊢
    rw [eval_eq_quadratic hp2] at h0 hm h2 ⊢
    exact abs_quadratic_le_three hab h0 hm h2 ht
  obtain ⟨hd1, hd2, -⟩ := derivWindow_whole hP hwin ht
  -- the hidden quadratic over the base point
  set x := gx l t with hx
  set z := Fin.init x
  set g := eval x (pderiv (3 : Fin 4) P) with hg
  set d := 4 * m₀ / s with hd
  have hd0 : 0 ≤ d := by positivity
  have hxz : x = (Fin.snoc z (x 3) : Fin 4 → ℝ) := (snoc_init_eq x).symm
  have hq : ∀ w : ℝ, eval (Function.update x (3 : Fin 4) w) P =
      eval x P + g * (w - x 3) + qc P / 2 * (w - x 3) ^ 2 := by
    intro w
    rw [update_three_eq_snoc, eval_quad_expand hP z (x 3) w, ← hxz]
  have hqw : ∀ w : ℝ, eval (Function.update x (3 : Fin 4) w) (pderiv (3 : Fin 4) P) =
      g + qc P * (w - x 3) := by
    intro w
    rw [update_three_eq_snoc, eval_pderiv_expand hP z (x 3) w, ← hxz]
  -- curvature times the window is small
  have hqcd : |qc P| * d ≤ s / 10 := by
    rw [hd]
    have : |qc P| * (4 * m₀ / s) = 4 * (|qc P| * m₀) / s := by ring
    rw [this, div_le_iff₀ hs]
    nlinarith
  -- the derivative stays in `[3s/4, 5s/4]` (in absolute value, with the sign of `g`) on the window
  have hwin' : ∀ w, |w - x 3| ≤ d → 8 / 10 * s ≤ |g + qc P * (w - x 3)| ∧
      |g + qc P * (w - x 3)| ≤ 12 / 10 * s ∧ (0 ≤ g + qc P * (w - x 3) ↔ 0 ≤ g) := by
    intro w hw
    have hsmall : |qc P * (w - x 3)| ≤ s / 10 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hw (abs_nonneg _)).trans hqcd
    have habs := abs_le.mp hsmall
    rcases le_or_gt 0 g with hg0 | hg0
    · rw [abs_of_nonneg hg0] at hd1 hd2
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
      · constructor <;> intro <;> linarith
    · rw [abs_of_neg hg0] at hd1 hd2
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
      · constructor <;> intro h <;> linarith
  -- a root in `[x 3 - d, x 3 + d]` by the intermediate value theorem
  have hcont : Continuous fun w : ℝ => eval (Function.update x (3 : Fin 4) w) P := by
    have : (fun w : ℝ => eval (Function.update x (3 : Fin 4) w) P) =
        fun w => eval x P + g * (w - x 3) + qc P / 2 * (w - x 3) ^ 2 := funext hq
    rw [this]; fun_prop
  -- values at the window ends have opposite signs (or vanish)
  have hend : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      σ * eval (Function.update x (3 : Fin 4) (x 3 + σ * d)) P * (if 0 ≤ g then 1 else -1) ≥ 0 := by
    intro σ hσ
    rw [hq]
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hval' := abs_le.mp hval
    have hgd : 8 / 10 * s * d ≤ |g| * d := by
      have := (hwin' (x 3) (by simp [hd0])).1
      simp only [sub_self, mul_zero, add_zero] at this
      exact mul_le_mul_of_nonneg_right this hd0
    have hsd : s * d = 4 * m₀ := by rw [hd]; field_simp
    have hqc2 : |qc P / 2 * (σ * d) ^ 2| ≤ s / 20 * d := by
      rw [abs_mul, abs_div, abs_two, mul_pow, hσ2, one_mul, abs_of_nonneg (sq_nonneg d)]
      have : |qc P| * d ≤ s / 10 := hqcd
      nlinarith
    have habs2 := abs_le.mp hqc2
    rcases le_or_gt 0 g with hg0 | hg0
    · rw [if_pos hg0, mul_one, abs_of_nonneg hg0] at *
      rcases hσ with h | h <;> subst h <;> nlinarith
    · rw [if_neg (not_le.mpr hg0), abs_of_neg hg0] at *
      rcases hσ with h | h <;> subst h <;> nlinarith
  have hroot : ∃ w₀ ∈ Set.Icc (x 3 - d) (x 3 + d), eval (Function.update x (3 : Fin 4) w₀) P = 0 := by
    have hle : x 3 - d ≤ x 3 + d := by linarith
    have hp := hend 1 (Or.inl rfl)
    have hn := hend (-1) (Or.inr rfl)
    simp only [one_mul, neg_one_mul, neg_mul] at hp hn
    have e1 : x 3 + -d = x 3 - d := by ring
    rw [e1] at hn
    rcases le_or_gt 0 g with hg0 | hg0
    · simp only [if_pos hg0, mul_one] at hp hn
      obtain ⟨w₀, hw₀, hz⟩ := intermediate_value_Icc hle hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
      exact ⟨w₀, hw₀, hz⟩
    · simp only [if_neg (not_le.mpr hg0), mul_neg, mul_one, neg_neg] at hp hn
      obtain ⟨w₀, hw₀, hz⟩ := intermediate_value_Icc' hle hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
      exact ⟨w₀, hw₀, hz⟩
  obtain ⟨w₀, hw₀, hz⟩ := hroot
  have hdist : |w₀ - x 3| ≤ d := abs_le.mpr ⟨by linarith [hw₀.1], by linarith [hw₀.2]⟩
  obtain ⟨b1, b2, -⟩ := hwin' w₀ hdist
  refine ⟨w₀, ?_, hz, ?_, ?_⟩
  · rw [abs_sub_comm]; exact hdist
  · rw [hqw]; linarith
  · rw [hqw]; linarith

section Format

theorem gfmt_ge_const {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (a : ℝ) :
    gfmt n 1 p.totalDegree {x | a ≤ eval x p} := by
  have h := gfmt_nonneg (p - C a)
  have hdeg : (p - C a).totalDegree ≤ p.totalDegree :=
    (totalDegree_sub _ _).trans (max_le le_rfl (by simp))
  have e : {x : Fin n → ℝ | 0 ≤ eval x (p - C a)} = {x | a ≤ eval x p} := by
    ext x; simp [sub_nonneg]
  rw [← e]; exact gfmt_mono le_rfl hdeg h

theorem gfmt_le_const {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (b : ℝ) :
    gfmt n 1 p.totalDegree {x | eval x p ≤ b} := by
  have h := gfmt_nonneg (C b - p)
  have hdeg : (C b - p).totalDegree ≤ p.totalDegree :=
    (totalDegree_sub _ _).trans (max_le (by simp) le_rfl)
  have e : {x : Fin n → ℝ | 0 ≤ eval x (C b - p)} = {x | eval x p ≤ b} := by
    ext x; simp [sub_nonneg]
  rw [← e]; exact gfmt_mono le_rfl hdeg h

/-- The slice of the root test set at a copy index has a fixed Boolean format. -/
theorem gfmt_rootTestSet {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {s m₀ ta tb : ℝ}
    (hm₀ : 0 ≤ m₀) (i : ℕ) :
    gfmt 6 11 4 {x | (i, x) ∈ rootTestSet P s m₀ ta tb} := by
  have hd1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 2 :=
    (totalDegree_pderiv_le' P (3 : Fin 4) (d := 1) hP).trans (by norm_num)
  -- value conditions
  have hv : ∀ t : ℝ, gfmt 6 1 4 {x : Fin 6 → ℝ | |eval (gx (i, x) t) P| ≤ m₀} := by
    intro t
    have h := gfmt_abs_le (slicePoly t P) hm₀
    have hdeg : 2 * (slicePoly t P).totalDegree ≤ 4 := by
      have := totalDegree_slicePoly_le t P; omega
    have e : {x : Fin 6 → ℝ | |eval x (slicePoly t P)| ≤ m₀} =
        {x | |eval (gx (i, x) t) P| ≤ m₀} := by
      ext x; simp only [Set.mem_ofPred_eq, eval_slicePoly t P i x]
    rw [← e]; exact gfmt_mono le_rfl hdeg h
  -- derivative conditions
  have hlo : ∀ (t a : ℝ) (σ : ℝ), gfmt 6 1 4
      {x : Fin 6 → ℝ | a ≤ σ * eval (gx (i, x) t) (pderiv 3 P)} := by
    intro t a σ
    have h := gfmt_ge_const (C σ * slicePoly t (pderiv 3 P)) a
    have hdeg : (C σ * slicePoly t (pderiv 3 P)).totalDegree ≤ 4 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_slicePoly_le t _).trans (hd1.trans (by norm_num))
    have e : {x : Fin 6 → ℝ | a ≤ eval x (C σ * slicePoly t (pderiv 3 P))} =
        {x | a ≤ σ * eval (gx (i, x) t) (pderiv 3 P)} := by
      ext x; simp only [Set.mem_ofPred_eq, map_mul, eval_C, eval_slicePoly t _ i x]
    rw [← e]; exact gfmt_mono le_rfl hdeg h
  have hhi : ∀ (t b : ℝ) (σ : ℝ), gfmt 6 1 4
      {x : Fin 6 → ℝ | σ * eval (gx (i, x) t) (pderiv 3 P) ≤ b} := by
    intro t b σ
    have h := gfmt_le_const (C σ * slicePoly t (pderiv 3 P)) b
    have hdeg : (C σ * slicePoly t (pderiv 3 P)).totalDegree ≤ 4 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_slicePoly_le t _).trans (hd1.trans (by norm_num))
    have e : {x : Fin 6 → ℝ | eval x (C σ * slicePoly t (pderiv 3 P)) ≤ b} =
        {x | σ * eval (gx (i, x) t) (pderiv 3 P) ≤ b} := by
      ext x; simp only [Set.mem_ofPred_eq, map_mul, eval_C, eval_slicePoly t _ i x]
    rw [← e]; exact gfmt_mono le_rfl hdeg h
  have hwin : ∀ σ : ℝ, gfmt 6 4 4 {x : Fin 6 → ℝ |
      9 / 10 * s ≤ σ * eval (gx (i, x) ta) (pderiv 3 P) ∧
      σ * eval (gx (i, x) ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
      9 / 10 * s ≤ σ * eval (gx (i, x) tb) (pderiv 3 P) ∧
      σ * eval (gx (i, x) tb) (pderiv 3 P) ≤ 11 / 10 * s} := by
    intro σ
    have h := gfmt_inter (hlo ta (9 / 10 * s) σ) (gfmt_inter (hhi ta (11 / 10 * s) σ)
      (gfmt_inter (hlo tb (9 / 10 * s) σ) (hhi tb (11 / 10 * s) σ)))
    have e : {x : Fin 6 → ℝ | 9 / 10 * s ≤ σ * eval (gx (i, x) ta) (pderiv 3 P)} ∩
        ({x | σ * eval (gx (i, x) ta) (pderiv 3 P) ≤ 11 / 10 * s} ∩
          ({x | 9 / 10 * s ≤ σ * eval (gx (i, x) tb) (pderiv 3 P)} ∩
            {x | σ * eval (gx (i, x) tb) (pderiv 3 P) ≤ 11 / 10 * s})) =
        {x : Fin 6 → ℝ | 9 / 10 * s ≤ σ * eval (gx (i, x) ta) (pderiv 3 P) ∧
          σ * eval (gx (i, x) ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
          9 / 10 * s ≤ σ * eval (gx (i, x) tb) (pderiv 3 P) ∧
          σ * eval (gx (i, x) tb) (pderiv 3 P) ≤ 11 / 10 * s} := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [e] at h
    exact gfmt_mono (by norm_num) (by simp) h
  have hall := gfmt_inter (hv ta) (gfmt_inter (hv ((ta + tb) / 2)) (gfmt_inter (hv tb)
    (gfmt_union (hwin 1) (hwin (-1)))))
  have e : {x | (i, x) ∈ rootTestSet P s m₀ ta tb} =
      {x : Fin 6 → ℝ | |eval (gx (i, x) ta) P| ≤ m₀} ∩
        ({x | |eval (gx (i, x) ((ta + tb) / 2)) P| ≤ m₀} ∩
          ({x | |eval (gx (i, x) tb) P| ≤ m₀} ∩
            ({x : Fin 6 → ℝ | 9 / 10 * s ≤ 1 * eval (gx (i, x) ta) (pderiv 3 P) ∧
              1 * eval (gx (i, x) ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
              9 / 10 * s ≤ 1 * eval (gx (i, x) tb) (pderiv 3 P) ∧
              1 * eval (gx (i, x) tb) (pderiv 3 P) ≤ 11 / 10 * s} ∪
            {x : Fin 6 → ℝ | 9 / 10 * s ≤ -1 * eval (gx (i, x) ta) (pderiv 3 P) ∧
              -1 * eval (gx (i, x) ta) (pderiv 3 P) ≤ 11 / 10 * s ∧
              9 / 10 * s ≤ -1 * eval (gx (i, x) tb) (pderiv 3 P) ∧
              -1 * eval (gx (i, x) tb) (pderiv 3 P) ≤ 11 / 10 * s}))) := by
    ext x
    simp only [rootTestSet, derivWindow, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union,
      one_mul, neg_one_mul]
  rw [e]
  exact gfmt_mono (by norm_num) (by simp) hall

end Format

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
