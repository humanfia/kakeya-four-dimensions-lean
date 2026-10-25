/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialRemez

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- If a polynomial is small relative to a known value at a nearby point,
then the test point lies near one of its complex roots. Unlike a monic
sublevel estimate, this is independent of the leading coefficient. -/
theorem polynomial_relative_small_eval_near_root (p : Polynomial ℂ)
    (x t : ℂ) (L δ M : ℝ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hxt : ‖x - t‖ ≤ L) (hx : M ≤ ‖p.eval x‖)
    (ht : ‖p.eval t‖ < M * (δ / (δ + L)) ^ p.natDegree) :
    ∃ z ∈ p.roots, ‖t - z‖ < δ := by
  classical
  by_contra! hfar
  have hterm (z : ℂ) (hz : z ∈ p.roots) : δ * ‖x - z‖ ≤ (δ + L) * ‖t - z‖ := by
    have htri : ‖x - z‖ ≤ L + ‖t - z‖ := by
      calc
        _ = ‖(x - t) + (t - z)‖ := by congr 1; ring
        _ ≤ ‖x - t‖ + ‖t - z‖ := norm_add_le _ _
        _ ≤ L + ‖t - z‖ := add_le_add hxt le_rfl
    have hscale := mul_le_mul_of_nonneg_left (hfar z hz) hL
    have htri' := mul_le_mul_of_nonneg_left htri hδ.le
    nlinarith
  have hsum : 0 < δ + L := by positivity
  have hcomparison (z : ℂ) (hz : z ∈ p.roots) :
      ‖x - z‖ ≤ ((δ + L) / δ) * ‖t - z‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using hterm z hz
  have hbound := Submission.Lib.K4PolynomialRemez.norm_eval_le_of_root_comparison
    p x t (div_nonneg hsum.le hδ.le) hcomparison
  have hstrict := mul_lt_mul_of_pos_left ht (pow_pos (div_pos hsum hδ) p.natDegree)
  have heq : ((δ + L) / δ) ^ p.natDegree * (M * (δ / (δ + L)) ^ p.natDegree) = M := by
    simp only [div_pow]
    field_simp
  rw [heq] at hstrict
  exact (not_lt_of_ge (hx.trans hbound)) hstrict

/-- A set lying in complex-root neighborhoods has an outer measure bound
linear in their common radius. -/
theorem volume_set_near_polynomial_roots_le (p : Polynomial ℂ) (E : Set ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ t ∈ E, ∃ z ∈ p.roots, ‖(t : ℂ) - z‖ < δ) :
    volume E ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * δ) := by
  classical
  have hsub : E ⊆ ⋃ z ∈ p.roots.toFinset, Set.Ioo (z.re - δ) (z.re + δ) := by
    intro t ht
    obtain ⟨z, hz, htz⟩ := hnear t ht
    have hre : |t - z.re| < δ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        (Complex.abs_re_le_norm ((t : ℂ) - z)).trans_lt htz
    refine Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨Multiset.mem_toFinset.mpr hz, ?_⟩⟩
    constructor <;> linarith [(abs_lt.mp hre).1, (abs_lt.mp hre).2]
  have hvol (z : ℂ) : volume (Set.Ioo (z.re - δ) (z.re + δ)) = ENNReal.ofReal (2 * δ) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  calc
    volume E ≤ ∑ z ∈ p.roots.toFinset, volume (Set.Ioo (z.re - δ) (z.re + δ)) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal ((p.roots.toFinset.card : ℝ) * (2 * δ)) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * δ) := by
      apply ENNReal.ofReal_le_ofReal
      have hcard : (p.roots.toFinset.card : ℝ) ≤ p.natDegree := by
        exact_mod_cast (p.roots.toFinset_card_le.trans_eq (IsAlgClosed.splits p).natDegree_eq_card_roots.symm)
      nlinarith

/-- A relative sublevel estimate on an interval, uniform in all polynomial
coefficients. A single large value determines the normalization. -/
theorem volume_polynomial_relative_sublevel (p : Polynomial ℂ)
    (s q δ M x : ℝ) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hx : x ∈ Set.Icc s (s + q)) (hlarge : M ≤ ‖p.eval (x : ℂ)‖) :
    volume {t : ℝ | t ∈ Set.Icc s (s + q) ∧
      ‖p.eval (t : ℂ)‖ < M * (δ / (δ + q)) ^ p.natDegree} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * δ) := by
  apply volume_set_near_polynomial_roots_le p _ δ hδ.le
  intro t ht
  have hdist : ‖(x : ℂ) - (t : ℂ)‖ ≤ q := by
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact abs_le.mpr ⟨by linarith [hx.1, ht.1.2], by linarith [hx.2, ht.1.1]⟩
  exact polynomial_relative_small_eval_near_root p (x : ℂ) (t : ℂ)
    q δ M hq hδ hdist hlarge ht.2

/-- A Remez bound at any complex point within bounded distance of a real
observation set. Only the outer measure of that set is needed. -/
theorem polynomial_remez_of_bounded_distance (p : Polynomial ℂ) (D : ℕ)
    (hD : p.natDegree ≤ D) (E : Set ℝ) (ℓ L ε : ℝ) (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    (hmass : ENNReal.ofReal ℓ ≤ volume E) (hsmall : ∀ t ∈ E, ‖p.eval (t : ℂ)‖ ≤ ε)
    (x : ℂ) (hdist : ∀ t ∈ E, ‖x - (t : ℂ)‖ ≤ L) :
    ‖p.eval x‖ ≤ (1 + 4 * (D + 1 : ℕ) * L / ℓ) ^ D * ε := by
  classical
  by_contra! hlarge
  let δ : ℝ := ℓ / (4 * (D + 1 : ℕ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum : 0 < δ + L := by positivity
  have hB : (δ + L) / δ = 1 + 4 * (D + 1 : ℕ) * L / ℓ := by
    dsimp [δ]
    field_simp
    <;> ring
  have hBpos : 0 < ((δ + L) / δ) ^ D := pow_pos (div_pos hsum hδ) D
  have heps : ε < ‖p.eval x‖ * (δ / (δ + L)) ^ D := by
    have h : ε < ‖p.eval x‖ / (((δ + L) / δ) ^ D) :=
      (lt_div_iff₀ hBpos).mpr (by simpa only [hB, mul_comm] using hlarge)
    change ε < ‖p.eval x‖ * ((((δ + L) / δ) ^ D)⁻¹) at h
    rw [← inv_pow, inv_div] at h
    exact h
  have hr0 : 0 ≤ δ / (δ + L) := (div_pos hδ hsum).le
  have hr1 : δ / (δ + L) ≤ 1 := (div_le_one hsum).mpr (by linarith)
  have hpow : (δ / (δ + L)) ^ D ≤ (δ / (δ + L)) ^ p.natDegree := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
    rw [hk, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1)
  have hnear (t : ℝ) (ht : t ∈ E) : ∃ z ∈ p.roots, ‖(t : ℂ) - z‖ < δ := by
    apply polynomial_relative_small_eval_near_root p x (t : ℂ) L δ ‖p.eval x‖ hL hδ (hdist t ht) le_rfl
    exact (hsmall t ht).trans_lt (heps.trans_le (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)))
  have hvol : volume E ≤ ENNReal.ofReal (ℓ / 2) := by
    apply (volume_set_near_polynomial_roots_le p E δ hδ.le hnear).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      2 * (p.natDegree : ℝ) * δ ≤ 2 * (D + 1 : ℕ) * δ := by
        gcongr
        exact_mod_cast Nat.le_succ_of_le hD
      _ = ℓ / 2 := by dsimp [δ]; field_simp; ring
  have hbad : ℓ ≤ ℓ / 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hvol)
  linarith

/-- The real interval form: small values on a positive-measure subset control
all values on the interval, uniformly in every polynomial coefficient. -/
theorem real_polynomial_remez_on_interval (p : Polynomial ℝ) (D : ℕ)
    (hD : p.natDegree ≤ D) (s q ℓ ε : ℝ) (hq : 0 ≤ q) (hℓ : 0 < ℓ)
    (E : Set ℝ) (hE : E ⊆ Set.Icc s (s + q)) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ t ∈ E, |p.eval t| ≤ ε) :
    ∀ x ∈ Set.Icc s (s + q), |p.eval x| ≤ (1 + 4 * (D + 1 : ℕ) * q / ℓ) ^ D * ε := by
  intro x hx
  have heval (t : ℝ) : ‖(p.map (algebraMap ℝ ℂ)).eval (t : ℂ)‖ = |p.eval t| := by
    rw [Polynomial.eval_map]
    change ‖p.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) t)‖ = _
    rw [Polynomial.eval₂_at_apply]
    exact Complex.norm_real _
  have hc := polynomial_remez_of_bounded_distance (p.map (algebraMap ℝ ℂ)) D
    (by simpa using hD) E ℓ q ε hℓ hq hmass (fun t ht => by rw [heval]; exact hsmall t ht)
    (x : ℂ) (fun t ht => by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      have ht' := hE ht
      exact abs_le.mpr ⟨by linarith [hx.1, ht'.2], by linarith [hx.2, ht'.1]⟩)
  simpa only [heval] using hc

end Submission.Lib.K4PolynomialNorming
