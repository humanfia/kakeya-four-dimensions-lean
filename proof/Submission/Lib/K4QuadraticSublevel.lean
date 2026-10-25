import Mathlib

/-!
# Quadratic sublevel estimates

Adapted from: here:o006

Lemma 2.9 of the supplied four-dimensional Kakeya paper. Splitting according to the
sign of the derivative gives two sets, each of diameter at most `2 * ε / b`.
-/

namespace Submission.Lib.K4QuadraticSublevel

open Set MeasureTheory Metric

/-- A polynomial of degree at most two has the usual three-coefficient form. -/
theorem quadratic_eq_coefficients (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) :
    ∃ a b c : ℝ,
      p = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c := by
  refine ⟨p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < 3 by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one]
  ring

/-- For a quadratic, its secant slope is the average of its endpoint derivatives. -/
theorem quadratic_eval_sub (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x y : ℝ) :
    2 * (p.eval y - p.eval x) =
      (y - x) * (p.derivative.eval x + p.derivative.eval y) := by
  obtain ⟨a, b, c, rfl⟩ := quadratic_eq_coefficients p hp
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num
  ring

private theorem quadratic_sub_le_of_derivative_ge (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2) {ε b x y : ℝ} (hb : 0 < b) (hxy : x ≤ y)
    (hx : |p.eval x| ≤ ε) (hy : |p.eval y| ≤ ε)
    (hdx : b ≤ p.derivative.eval x) (hdy : b ≤ p.derivative.eval y) :
    y - x ≤ 2 * ε / b := by
  apply (le_div_iff₀ hb).2
  have hprod := mul_le_mul_of_nonneg_left (add_le_add hdx hdy) (sub_nonneg.mpr hxy)
  rw [← quadratic_eval_sub p hp x y] at hprod
  have hx' := (abs_le.mp hx).1
  have hy' := (abs_le.mp hy).2
  nlinarith

/-- A derivative-sign component of a quadratic regular sublevel set has small diameter. -/
theorem quadratic_dist_le_of_derivative_ge (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2) {ε b x y : ℝ} (hb : 0 < b)
    (hx : |p.eval x| ≤ ε) (hy : |p.eval y| ≤ ε)
    (hdx : b ≤ p.derivative.eval x) (hdy : b ≤ p.derivative.eval y) :
    dist x y ≤ 2 * ε / b := by
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using
      quadratic_sub_le_of_derivative_ge p hp hb hxy hx hy hdx hdy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using
      quadratic_sub_le_of_derivative_ge p hp hb hyx hy hx hdy hdx

/-- The increasing component has outer Lebesgue measure at most `2 * ε / b`. -/
theorem volume_quadratic_sublevel_derivative_ge (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 2) {ε b : ℝ} (hb : 0 < b) :
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ≤
      ENNReal.ofReal (2 * ε / b) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
  intro x hx y hy
  exact quadratic_dist_le_of_derivative_ge p hp hb hx.1 hy.1 hx.2 hy.2

/-- Quadratic sublevel estimate, Lemma 2.9 of the supplied paper. -/
theorem volume_quadratic_sublevel (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) :
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ≤
      ENNReal.ofReal (4 * ε / b) := by
  have hneg : (-p).natDegree ≤ 2 := by simpa using hp
  have hsub : {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ⊆
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ∪
      {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x} := by
    intro x hx
    by_cases hd : 0 ≤ p.derivative.eval x
    · exact Or.inl ⟨hx.1, by simpa only [abs_of_nonneg hd] using hx.2⟩
    · refine Or.inr ⟨by simpa using hx.1, ?_⟩
      simpa only [Polynomial.derivative_neg, Polynomial.eval_neg,
        abs_of_neg (lt_of_not_ge hd)] using hx.2
  calc
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ≤
        volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} +
        volume {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * ε / b) + ENNReal.ofReal (2 * ε / b) :=
      add_le_add (volume_quadratic_sublevel_derivative_ge p hp hb)
        (volume_quadratic_sublevel_derivative_ge (-p) hneg hb)
    _ = ENNReal.ofReal (4 * ε / b) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A set of diameter at most `L` occupies at most `2 * L / δ + 2` bins of a shifted grid.
The bound uses any point of the set as the center of a containing interval. -/
theorem grid_bins_of_pairwise_dist_le (s : Set ℝ) {L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 < δ) (o : ℝ)
    (hs : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ L) :
    ((fun x : ℝ => ⌊(x - o) / δ⌋) '' s).Finite ∧
      (((fun x : ℝ => ⌊(x - o) / δ⌋) '' s).ncard : ℝ) ≤ 2 * L / δ + 2 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp only [Set.image_empty, Set.finite_empty, Set.ncard_empty, Nat.cast_zero,
      true_and]
    positivity
  let lo : ℤ := ⌊(a - L - o) / δ⌋
  let hi : ℤ := ⌊(a + L - o) / δ⌋
  have hlohi : lo ≤ hi := Int.floor_mono
    (div_le_div_of_nonneg_right (by linarith : a - L - o ≤ a + L - o) hδ.le)
  have hsub : (fun x : ℝ => ⌊(x - o) / δ⌋) '' s ⊆ Set.Icc lo hi := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : |x - a| ≤ L := by simpa only [Real.dist_eq] using hs x hx a ha
    have hxa := abs_le.mp hx'
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le)⟩
  refine ⟨(Set.finite_Icc lo hi).subset hsub, ?_⟩
  calc
    (((fun x : ℝ => ⌊(x - o) / δ⌋) '' s).ncard : ℝ) ≤
        ((Set.Icc lo hi).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub (Set.finite_Icc lo hi)
    _ = (hi : ℝ) + 1 - lo := by
      rw [Set.ncard_Icc, Int.card_Icc]
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ hi + 1 - lo)
    _ ≤ (a + L - o) / δ + 1 - ((a - L - o) / δ - 1) := by
      have hh : (hi : ℝ) ≤ (a + L - o) / δ := Int.floor_le _
      have hl : (a - L - o) / δ - 1 < (lo : ℝ) := Int.sub_one_lt_floor _
      linarith
    _ = 2 * L / δ + 2 := by ring

/-- An increasing derivative component has only boundedly many grid bins. -/
theorem grid_bins_quadratic_derivative_ge (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {ε b δ : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hδ : 0 < δ) (o : ℝ) :
    ((fun x : ℝ => ⌊(x - o) / δ⌋) ''
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x}).Finite ∧
    (((fun x : ℝ => ⌊(x - o) / δ⌋) ''
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x}).ncard : ℝ) ≤
        4 * ε / (b * δ) + 2 := by
  have h := grid_bins_of_pairwise_dist_le
    {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x}
    (show 0 ≤ 2 * ε / b by positivity) hδ o (by
      intro x hx y hy
      exact quadratic_dist_le_of_derivative_ge p hp hb hx.1 hy.1 hx.2 hy.2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

/-- Grid-bin form of Lemma 2.9, with an absolute constant and arbitrary grid origin. -/
theorem grid_bins_quadratic_sublevel (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {ε b δ : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hδ : 0 < δ) (o : ℝ) :
    ((fun x : ℝ => ⌊(x - o) / δ⌋) ''
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|}).Finite ∧
    (((fun x : ℝ => ⌊(x - o) / δ⌋) ''
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|}).ncard : ℝ) ≤
        8 * (1 + ε / (b * δ)) := by
  have hneg : (-p).natDegree ≤ 2 := by simpa using hp
  have hpos := grid_bins_quadratic_derivative_ge p hp hε hb hδ o
  have hneg' := grid_bins_quadratic_derivative_ge (-p) hneg hε hb hδ o
  have hsub : (fun x : ℝ => ⌊(x - o) / δ⌋) ''
        {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ⊆
      (fun x : ℝ => ⌊(x - o) / δ⌋) ''
        {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ∪
      (fun x : ℝ => ⌊(x - o) / δ⌋) ''
        {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x} := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hd : 0 ≤ p.derivative.eval x
    · exact Or.inl ⟨x, ⟨hx.1, by simpa only [abs_of_nonneg hd] using hx.2⟩, rfl⟩
    · refine Or.inr ⟨x, ⟨by simpa using hx.1, ?_⟩, rfl⟩
      simpa only [Polynomial.derivative_neg, Polynomial.eval_neg,
        abs_of_neg (lt_of_not_ge hd)] using hx.2
  refine ⟨(hpos.1.union hneg'.1).subset hsub, ?_⟩
  have hn := (Set.ncard_le_ncard hsub (hpos.1.union hneg'.1)).trans
    (Set.ncard_union_le _ _)
  have hn' : (((fun x : ℝ => ⌊(x - o) / δ⌋) ''
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|}).ncard : ℝ) ≤
      (((fun x : ℝ => ⌊(x - o) / δ⌋) ''
        {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x}).ncard : ℝ) +
      (((fun x : ℝ => ⌊(x - o) / δ⌋) ''
        {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x}).ncard : ℝ) := by
    exact_mod_cast hn
  refine (hn'.trans (add_le_add hpos.2 hneg'.2)).trans ?_
  ring_nf
  linarith

end Submission.Lib.K4QuadraticSublevel
