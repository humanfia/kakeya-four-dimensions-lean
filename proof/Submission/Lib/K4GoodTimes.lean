import Mathlib

/-!
# Small-value sets of monic polynomials

Adapted from: here:o006

The root-neighborhood estimate used in the good-time argument of Theorem 2.17
of the supplied Kakeya paper. It is uniform in every coefficient.
-/

namespace Submission.Lib.K4GoodTimes

open Set MeasureTheory

/-- A small value of a monic polynomial lies near one of its complex roots. -/
theorem monic_small_eval_near_root (p : Polynomial ℂ) (hp : p.Monic)
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℂ) (hx : ‖p.eval x‖ < ε ^ p.natDegree) :
    ∃ z ∈ p.roots, ‖x - z‖ < ε := by
  have hs := IsAlgClosed.splits p
  have hnorm : (p.roots.map (fun z => ‖x - z‖)).prod = ‖p.eval x‖ := by
    calc
      _ = (p.roots.map (fun z => NormedField.toMulRingNorm ℂ (x - z))).prod := rfl
      _ = ‖(p.roots.map (fun z => x - z)).prod‖ := by
        exact p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun z => x - z)
      _ = ‖p.eval x‖ := by rw [hs.eval_eq_prod_roots_of_monic hp]
  by_contra! h
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ => ε)
    (fun z => ‖x - z‖) (by intro z hz; exact hε) h
  simp only [Multiset.map_const', Multiset.prod_replicate,
    ← hs.natDegree_eq_card_roots] at hprod
  rw [hnorm] at hprod
  exact (not_lt_of_ge hprod) hx

/-- The real small-value set lies in root neighborhoods of total length at most `2 * degree * ε`. -/
theorem volume_monic_sublevel (p : Polynomial ℂ) (hp : p.Monic)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume {t : ℝ | ‖p.eval (t : ℂ)‖ < ε ^ p.natDegree} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * ε) := by
  classical
  have hsub : {t : ℝ | ‖p.eval (t : ℂ)‖ < ε ^ p.natDegree} ⊆
      ⋃ z ∈ p.roots.toFinset, Set.Ioo (z.re - ε) (z.re + ε) := by
    intro t ht
    obtain ⟨z, hz, htz⟩ := monic_small_eval_near_root p hp hε (t : ℂ) ht
    have hre : |t - z.re| < ε := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        (Complex.abs_re_le_norm ((t : ℂ) - z)).trans_lt htz
    have hre' := abs_lt.mp hre
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2
      ⟨Multiset.mem_toFinset.mpr hz, by constructor <;> linarith⟩⟩
  have hvol (z : ℂ) : volume (Set.Ioo (z.re - ε) (z.re + ε)) =
      ENNReal.ofReal (2 * ε) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  calc
    volume {t : ℝ | ‖p.eval (t : ℂ)‖ < ε ^ p.natDegree} ≤
        ∑ z ∈ p.roots.toFinset, volume (Set.Ioo (z.re - ε) (z.re + ε)) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal ((p.roots.toFinset.card : ℝ) * (2 * ε)) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * ε) := by
      apply ENNReal.ofReal_le_ofReal
      have hcard : (p.roots.toFinset.card : ℝ) ≤ (p.natDegree : ℝ) := by
        exact_mod_cast (p.roots.toFinset_card_le.trans_eq
          (IsAlgClosed.splits p).natDegree_eq_card_roots.symm)
      nlinarith

/-- The same estimate for a real monic polynomial, without exposing its complex roots. -/
theorem volume_real_monic_sublevel (p : Polynomial ℝ) (hp : p.Monic)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume {t : ℝ | |p.eval t| < ε ^ p.natDegree} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * ε) := by
  have h := volume_monic_sublevel (p.map (algebraMap ℝ ℂ))
    (hp.map (algebraMap ℝ ℂ)) hε
  have heval (t : ℝ) : ‖(p.map (algebraMap ℝ ℂ)).eval (t : ℂ)‖ = |p.eval t| := by
    rw [Polynomial.eval_map]
    change ‖p.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) t)‖ = _
    rw [Polynomial.eval₂_at_apply]
    exact Complex.norm_real _
  simpa only [Polynomial.natDegree_map, heval] using h

/-- Determinant form of the root-neighborhood estimate, uniform in the matrix. -/
theorem volume_det_add_scalar_sublevel {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume {t : ℝ | |(A + Matrix.scalar (Fin d) t).det| < ε ^ d} ≤
      ENNReal.ofReal (2 * (d : ℝ) * ε) := by
  have h := volume_real_monic_sublevel (-A).charpoly (Matrix.charpoly_monic _) hε
  simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Matrix.eval_charpoly,
    sub_neg_eq_add, add_comm] using h

/-- If an affine function reaches magnitude `M` on an interval of length `q`, the times
where its magnitude is smaller than `ε ≤ M / 2` have total length at most `4 * ε * q / M`. -/
theorem volume_affine_sublevel_on_interval (a b s q M ε : ℝ)
    (hq : 0 < q) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M / 2)
    (hlarge : ∃ t ∈ Set.Icc s (s + q), M ≤ |a * t + b|) :
    volume {t : ℝ | t ∈ Set.Icc s (s + q) ∧ |a * t + b| < ε} ≤
      ENNReal.ofReal (4 * ε * q / M) := by
  let S : Set ℝ := {t : ℝ | t ∈ Set.Icc s (s + q) ∧ |a * t + b| < ε}
  change volume S ≤ _
  rcases S.eq_empty_or_nonempty with hempty | ⟨t₁, ht₁⟩
  · simp [hempty]
  obtain ⟨t₀, ht₀, hlarge⟩ := hlarge
  have hdist : |t₀ - t₁| ≤ q := abs_le.mpr ⟨by linarith [ht₀.1, ht₁.1.2],
    by linarith [ht₁.1.1, ht₀.2]⟩
  have hidentity (x y : ℝ) : (a * x + b) - (a * y + b) = a * (x - y) := by ring
  have htriangle : |a * t₀ + b| ≤ |a| * q + |a * t₁ + b| := by
    calc
      _ ≤ |(a * t₀ + b) - (a * t₁ + b)| + |a * t₁ + b| := by
        simpa only [sub_zero] using abs_sub_le (a * t₀ + b) (a * t₁ + b) 0
      _ = |a| * |t₀ - t₁| + |a * t₁ + b| := by rw [hidentity, abs_mul]
      _ ≤ |a| * q + |a * t₁ + b| :=
        add_le_add (mul_le_mul_of_nonneg_left hdist (abs_nonneg a)) le_rfl
  have hslope : M ≤ 2 * |a| * q := by linarith [ht₁.2]
  have ha : 0 < |a| := by nlinarith [abs_nonneg a]
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * ε / |a| := by
    intro x hx y hy
    apply (le_div_iff₀ ha).2
    calc
      dist x y * |a| = |(a * x + b) - (a * y + b)| := by
        rw [Real.dist_eq, hidentity, abs_mul]
        ring
      _ ≤ |a * x + b| + |a * y + b| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a * x + b) 0 (a * y + b)
      _ ≤ 2 * ε := by linarith [hx.2, hy.2]
  calc
    volume S ≤ ENNReal.ofReal (2 * ε / |a|) :=
      (Real.volume_le_diam S).trans (Metric.ediam_le_of_forall_dist_le hdiam)
    _ ≤ ENNReal.ofReal (4 * ε * q / M) := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_iff₀ ha hM).2
      have hmul := mul_le_mul_of_nonneg_left hslope (show 0 ≤ 2 * ε by positivity)
      nlinarith

/-- The determinant and native-derivative good times overlap on at least half the interval.
This is the good-time step in the slope-volume proof of Theorem 2.17. -/
theorem volume_det_affine_good_times (A : Matrix (Fin 3) (Fin 3) ℝ)
    (a b s q K : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hlarge : ∃ t ∈ Set.Icc s (s + q), K⁻¹ ≤ |a * t + b|) :
    ENNReal.ofReal (q / 2) ≤ volume {t : ℝ | t ∈ Set.Icc s (s + q) ∧
      (q / 24) ^ 3 ≤ |(A + Matrix.scalar (Fin 3) t).det| ∧
      K⁻¹ / 16 ≤ |a * t + b|} := by
  let G : Set ℝ := {t : ℝ | t ∈ Set.Icc s (s + q) ∧
    (q / 24) ^ 3 ≤ |(A + Matrix.scalar (Fin 3) t).det| ∧
    K⁻¹ / 16 ≤ |a * t + b|}
  let BD : Set ℝ := {t : ℝ | |(A + Matrix.scalar (Fin 3) t).det| < (q / 24) ^ 3}
  let BA : Set ℝ := {t : ℝ | t ∈ Set.Icc s (s + q) ∧ |a * t + b| < K⁻¹ / 16}
  have hD : volume BD ≤ ENNReal.ofReal (q / 4) := by
    have h := volume_det_add_scalar_sublevel A (show 0 ≤ q / 24 by positivity)
    convert h using 1
    congr 1
    ring
  have hA : volume BA ≤ ENNReal.ofReal (q / 4) := by
    have hKi : 0 < K⁻¹ := inv_pos.mpr hK
    have h := volume_affine_sublevel_on_interval a b s q K⁻¹ (K⁻¹ / 16)
      hq hKi (by positivity) (by linarith) hlarge
    convert h using 1
    congr 1
    field_simp
    ring
  have hcover : Set.Icc s (s + q) ⊆ G ∪ (BD ∪ BA) := by
    intro t ht
    by_cases hd : (q / 24) ^ 3 ≤ |(A + Matrix.scalar (Fin 3) t).det|
    · by_cases ha : K⁻¹ / 16 ≤ |a * t + b|
      · exact Or.inl ⟨ht, hd, ha⟩
      · exact Or.inr (Or.inr ⟨ht, lt_of_not_ge ha⟩)
    · exact Or.inr (Or.inl (lt_of_not_ge hd))
  have htotal : ENNReal.ofReal q ≤ volume G + ENNReal.ofReal (q / 2) := by
    calc
      ENNReal.ofReal q = volume (Set.Icc s (s + q)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      _ ≤ volume G + volume (BD ∪ BA) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ volume G + (volume BD + volume BA) :=
        add_le_add le_rfl (measure_union_le _ _)
      _ ≤ volume G + (ENNReal.ofReal (q / 4) + ENNReal.ofReal (q / 4)) :=
        add_le_add le_rfl (add_le_add hD hA)
      _ = volume G + ENNReal.ofReal (q / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
  have hsplit : ENNReal.ofReal q =
      ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hsplit] at htotal
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top htotal

end Submission.Lib.K4GoodTimes
