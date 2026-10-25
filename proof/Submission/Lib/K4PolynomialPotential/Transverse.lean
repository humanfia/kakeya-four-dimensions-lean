import Mathlib

/-!
Adapted from: here:o062
Original proof: x0212, commit 72725d2,
Submission/Obl/k4_scalar_mesh_projection/Transverse.lean.

Regular sublevel sets of real polynomials. Counting roots of the shifted
derivative partitions the line into finitely many pieces with a uniform
inverse-Lipschitz bound on the relevant derivative branch.
-/

namespace Submission.Lib.K4PolynomialPotential

open Set MeasureTheory

noncomputable def polynomialRootRank (p : Polynomial ℝ) (x : ℝ) : ℕ := by
  classical
  exact (p.roots.toFinset.filter (fun r => r < x)).card

theorem polynomialRootRank_le (p : Polynomial ℝ) (x : ℝ) :
    polynomialRootRank p x ≤ p.roots.toFinset.card := by
  classical
  exact Finset.card_filter_le _ _

theorem no_root_between_of_equal_polynomialRootRank (p : Polynomial ℝ) (hp : p ≠ 0)
    {x y : ℝ} (hxy : x ≤ y) (h : polynomialRootRank p x = polynomialRootRank p y) :
    ∀ z ∈ Ico x y, p.eval z ≠ 0 := by
  classical
  have hsub : p.roots.toFinset.filter (fun r => r < x) ⊆
      p.roots.toFinset.filter (fun r => r < y) := by
    intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.trans_le hxy⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    change polynomialRootRank p y ≤ polynomialRootRank p x
    exact h.ge)
  intro z hz hzero
  have hzroot : z ∈ p.roots.toFinset := by
    simpa only [Multiset.mem_toFinset] using (Polynomial.mem_roots hp).mpr hzero
  have hzy : z ∈ p.roots.toFinset.filter (fun r => r < y) :=
    Finset.mem_filter.mpr ⟨hzroot, hz.2⟩
  rw [← heq] at hzy
  have hzx := (Finset.mem_filter.mp hzy).2
  exact (not_lt_of_ge hz.1) hzx

theorem polynomial_nonneg_between_of_equal_rootRank (p : Polynomial ℝ)
    {x y : ℝ} (hxy : x ≤ y) (h : polynomialRootRank p x = polynomialRootRank p y)
    (hx : 0 ≤ p.eval x) (hy : 0 ≤ p.eval y) :
    ∀ z ∈ Icc x y, 0 ≤ p.eval z := by
  by_cases hp : p = 0
  · subst p
    simp
  have hroot := no_root_between_of_equal_polynomialRootRank p hp hxy h
  intro z hz
  by_cases hzy : z = y
  · simpa only [hzy] using hy
  by_contra hneg
  have hzneg : p.eval z < 0 := lt_of_not_ge hneg
  have hxpos : 0 < p.eval x := by
    apply lt_of_le_of_ne hx
    intro hzero
    exact hroot x ⟨le_rfl, hz.1.trans_lt (lt_of_le_of_ne hz.2 hzy)⟩ hzero.symm
  obtain ⟨r, hr, hpr⟩ := intermediate_value_Icc' hz.1
    p.continuous.continuousOn (show 0 ∈ Icc (p.eval z) (p.eval x) from
      ⟨hzneg.le, hxpos.le⟩)
  exact hroot r ⟨hr.1, hr.2.trans_lt (lt_of_le_of_ne hz.2 hzy)⟩ hpr

theorem polynomial_dist_le_of_derivative_ge_same_rank (p : Polynomial ℝ)
    {ε b x y : ℝ} (hb : 0 < b)
    (hx : |p.eval x| ≤ ε) (hy : |p.eval y| ≤ ε)
    (hdx : b ≤ p.derivative.eval x) (hdy : b ≤ p.derivative.eval y)
    (hrank : polynomialRootRank (p.derivative - Polynomial.C b) x =
      polynomialRootRank (p.derivative - Polynomial.C b) y) :
    dist x y ≤ 2 * ε / b := by
  wlog hxy : x ≤ y generalizing x y with hswap
  · simpa only [dist_comm] using
      hswap hy hx hdy hdx hrank.symm (le_of_not_ge hxy)
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · have hε : 0 ≤ ε := (abs_nonneg _).trans hx
    simp only [dist_self]
    positivity
  have hder : ∀ z ∈ Icc x y, b ≤ p.derivative.eval z := by
    intro z hz
    have hnonneg := polynomial_nonneg_between_of_equal_rootRank
      (p.derivative - Polynomial.C b) hxy hrank
      (by simpa using sub_nonneg.mpr hdx)
      (by simpa using sub_nonneg.mpr hdy) z hz
    simpa only [Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg] using hnonneg
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun t => p.eval t) (fun t => p.derivative.eval t) hlt
    p.continuous.continuousOn (fun t ht => p.hasDerivAt t)
  have hs := (hder c ⟨hc.1.le, hc.2.le⟩)
  rw [hslope] at hs
  have hprod := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
  have hpx := (abs_le.mp hx).1
  have hpy := (abs_le.mp hy).2
  have hlen : y - x ≤ 2 * ε / b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hlen

/-- A regular increasing sublevel set has at most degree-plus-one pieces,
each with the first-derivative diameter bound. No measurability premise on a
subset of the sublevel set is needed. -/
theorem volume_polynomial_sublevel_derivative_ge (p : Polynomial ℝ)
    {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) :
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ≤
      ENNReal.ofReal (2 * ((p.natDegree : ℝ) + 1) * ε / b) := by
  classical
  let q : Polynomial ℝ := p.derivative - Polynomial.C b
  let piece (i : Fin (q.roots.toFinset.card + 1)) : Set ℝ :=
    {x | (|p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x) ∧ polynomialRootRank q x = i.val}
  have hcover : {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ⊆ ⋃ i, piece i := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨⟨polynomialRootRank q x, Nat.lt_succ_of_le (polynomialRootRank_le q x)⟩,
      hx, rfl⟩
  have hpiece (i : Fin (q.roots.toFinset.card + 1)) :
      volume (piece i) ≤ ENNReal.ofReal (2 * ε / b) := by
    refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
    intro x hx y hy
    exact polynomial_dist_le_of_derivative_ge_same_rank p hb
      hx.1.1 hy.1.1 hx.1.2 hy.1.2 (hx.2.trans hy.2.symm)
  have hqdegree : q.natDegree ≤ p.natDegree := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_zero]
    exact (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have hcard : q.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' q).trans hqdegree)
  calc
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ≤ volume (⋃ i, piece i) :=
      measure_mono hcover
    _ ≤ ∑ i, volume (piece i) := measure_iUnion_fintype_le volume piece
    _ ≤ ∑ _i : Fin (q.roots.toFinset.card + 1), ENNReal.ofReal (2 * ε / b) :=
      Finset.sum_le_sum (fun i hi => hpiece i)
    _ = ENNReal.ofReal (((q.roots.toFinset.card + 1 : ℕ) : ℝ) * (2 * ε / b)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * ((p.natDegree : ℝ) + 1) * ε / b) := by
      apply ENNReal.ofReal_le_ofReal
      have hc : ((q.roots.toFinset.card + 1 : ℕ) : ℝ) ≤ (p.natDegree : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right hcard 1
      have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * ε / b by positivity)
      exact hh.trans_eq (by ring)

/-- Polynomial regular sublevel estimate of any fixed degree, with linear
dependence on the height-window width. -/
theorem volume_polynomial_regular_sublevel (p : Polynomial ℝ)
    {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) :
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ≤
      ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * ε / b) := by
  have hcover : {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ⊆
      {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} ∪
        {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x} := by
    intro x hx
    by_cases hsign : 0 ≤ p.derivative.eval x
    · exact Or.inl ⟨hx.1, by simpa only [abs_of_nonneg hsign] using hx.2⟩
    · refine Or.inr ⟨by simpa using hx.1, ?_⟩
      simpa only [Polynomial.derivative_neg, Polynomial.eval_neg,
        abs_of_neg (lt_of_not_ge hsign)] using hx.2
  calc
    volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ |p.derivative.eval x|} ≤
        volume {x : ℝ | |p.eval x| ≤ ε ∧ b ≤ p.derivative.eval x} +
          volume {x : ℝ | |(-p).eval x| ≤ ε ∧ b ≤ (-p).derivative.eval x} :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * ((p.natDegree : ℝ) + 1) * ε / b) +
        ENNReal.ofReal (2 * ((p.natDegree : ℝ) + 1) * ε / b) := by
      apply add_le_add (volume_polynomial_sublevel_derivative_ge p hε hb)
      simpa only [Polynomial.natDegree_neg] using
        volume_polynomial_sublevel_derivative_ge (-p) hε hb
    _ = ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * ε / b) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A translated height window has the same regular-sublevel estimate. -/
theorem volume_polynomial_regular_height_window (p : Polynomial ℝ)
    (c : ℝ) {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) :
    volume {x : ℝ | |p.eval x - c| ≤ ε ∧ b ≤ |p.derivative.eval x|} ≤
      ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * ε / b) := by
  have h := volume_polynomial_regular_sublevel (p - Polynomial.C c) hε hb
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.derivative_sub,
    Polynomial.derivative_C, sub_zero] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hdegree : (p - Polynomial.C c).natDegree ≤ p.natDegree := by
    simpa only [Polynomial.natDegree_C, max_zero] using
      Polynomial.natDegree_sub_le p (Polynomial.C c)
  have hcast : (((p - Polynomial.C c).natDegree : ℝ) + 1) ≤ (p.natDegree : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hdegree 1
  have hm := mul_le_mul_of_nonneg_right hcast (show 0 ≤ 4 * ε / b by positivity)
  convert hm using 1 <;> ring

/-- On a fiber with derivative bounded away from zero, the measure occupied
by finitely many height windows is linear in their number and width. -/
theorem volume_polynomial_regular_height_windows {ι : Type*} (p : Polynomial ℝ)
    (F : Finset ι) (c : ι → ℝ) {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) :
    volume {x : ℝ | b ≤ |p.derivative.eval x| ∧ ∃ i ∈ F, |p.eval x - c i| ≤ ε} ≤
      ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * (F.card : ℝ) * ε / b) := by
  classical
  have hcover : {x : ℝ | b ≤ |p.derivative.eval x| ∧ ∃ i ∈ F, |p.eval x - c i| ≤ ε} ⊆
      ⋃ i ∈ F, {x : ℝ | |p.eval x - c i| ≤ ε ∧ b ≤ |p.derivative.eval x|} := by
    rintro x ⟨hx, i, hi, hxi⟩
    simp only [mem_iUnion]
    exact ⟨i, hi, hxi, hx⟩
  calc
    volume {x : ℝ | b ≤ |p.derivative.eval x| ∧ ∃ i ∈ F, |p.eval x - c i| ≤ ε} ≤
        volume (⋃ i ∈ F, {x : ℝ | |p.eval x - c i| ≤ ε ∧ b ≤ |p.derivative.eval x|}) :=
      measure_mono hcover
    _ ≤ ∑ i ∈ F, volume {x : ℝ | |p.eval x - c i| ≤ ε ∧ b ≤ |p.derivative.eval x|} :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _i ∈ F, ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * ε / b) :=
      Finset.sum_le_sum (fun i hi => volume_polynomial_regular_height_window p (c i) hε hb)
    _ = ENNReal.ofReal ((F.card : ℝ) * (4 * ((p.natDegree : ℝ) + 1) * ε / b)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (4 * ((p.natDegree : ℝ) + 1) * (F.card : ℝ) * ε / b) := by
      congr 1
      ring

end Submission.Lib.K4PolynomialPotential
