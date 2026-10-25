import Mathlib

/-!
Truncated energy estimates from finite-scale interval bounds.
-/

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped BigOperators

private theorem dyadic_energy_weight {C s t : ℝ} (n : ℕ) :
    ((1 / 2 : ℝ) ^ (n + 1)) ^ (-t) * (C * ((1 / 2 : ℝ) ^ n) ^ s) =
      (C * (1 / 2 : ℝ) ^ (-t)) * ((1 / 2 : ℝ) ^ (s - t)) ^ n := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have heq : ((1 / 2 : ℝ) ^ n) ^ (-t) * ((1 / 2 : ℝ) ^ n) ^ s =
      ((1 / 2 : ℝ) ^ (s - t)) ^ n := by
    rw [← Real.rpow_add hp, sub_eq_add_neg, add_comm s,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [pow_succ, Real.mul_rpow hp.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc _ = (C * (1 / 2 : ℝ) ^ (-t)) *
      (((1 / 2 : ℝ) ^ n) ^ (-t) * ((1 / 2 : ℝ) ^ n) ^ s) := by ring
    _ = _ := by rw [heq]

/-- A distribution bound controls every smaller negative moment. -/
theorem lintegral_rpow_neg_le_of_distribution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    {C s t : ℝ} (hf : Measurable f) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hst : t < s)
    (hf_bounds : ∀ x, 0 < f x ∧ f x ≤ 1)
    (hcount : ∀ u : ℝ, 0 < u →
      μ {x | f x ≤ u} ≤ ENNReal.ofReal (C * u ^ s)) :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ (-t)) ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  classical
  let shell (n : ℕ) : α → ENNReal :=
    {x | f x ≤ (1 / 2 : ℝ) ^ n}.indicator
      (fun _ => ENNReal.ofReal (((1 / 2 : ℝ) ^ (n + 1)) ^ (-t)))
  have hmajor (x : α) :
      ENNReal.ofReal ((f x) ^ (-t)) ≤ ∑' n, shell n x := by
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one
      (hf_bounds x).1 (hf_bounds x).2
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    calc ENNReal.ofReal ((f x) ^ (-t)) ≤
          ENNReal.ofReal (((1 / 2 : ℝ) ^ (n + 1)) ^ (-t)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_nonpos (by positivity) hn.le (neg_nonpos.mpr ht))
      _ = shell n x := by
        dsimp [shell]
        rw [indicator_of_mem (show x ∈ {x | f x ≤ (1 / 2 : ℝ) ^ n} from hn')]
      _ ≤ ∑' n, shell n x := ENNReal.le_tsum (f := fun k => shell k x) n
  have hshell (n : ℕ) :
      (∫⁻ x, shell n x ∂μ) ≤
        ENNReal.ofReal ((C * (1 / 2 : ℝ) ^ (-t)) *
          ((1 / 2 : ℝ) ^ (s - t)) ^ n) := by
    rw [show (∫⁻ x, shell n x ∂μ) =
        ENNReal.ofReal (((1 / 2 : ℝ) ^ (n + 1)) ^ (-t)) *
          μ {x | f x ≤ (1 / 2 : ℝ) ^ n} by
      exact lintegral_indicator_const (measurableSet_le hf measurable_const) _]
    calc _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ (n + 1)) ^ (-t)) *
          ENNReal.ofReal (C * ((1 / 2 : ℝ) ^ n) ^ s) :=
        mul_le_mul' le_rfl (hcount _ (by positivity))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), dyadic_energy_weight]
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (s - t) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (s - t) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hst)
  have hsum : Summable (fun n : ℕ =>
      (C * (1 / 2 : ℝ) ^ (-t)) * ((1 / 2 : ℝ) ^ (s - t)) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc (∫⁻ x, ENNReal.ofReal ((f x) ^ (-t)) ∂μ) ≤
        ∫⁻ x, ∑' n, shell n x ∂μ := lintegral_mono hmajor
    _ = ∑' n, ∫⁻ x, shell n x ∂μ :=
      lintegral_tsum (fun n =>
        (measurable_const.indicator (measurableSet_le hf measurable_const)).aemeasurable)
    _ ≤ ∑' n, ENNReal.ofReal ((C * (1 / 2 : ℝ) ^ (-t)) *
        ((1 / 2 : ℝ) ^ (s - t)) ^ n) := ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (∑' n : ℕ,
        (C * (1 / 2 : ℝ) ^ (-t)) * ((1 / 2 : ℝ) ^ (s - t)) ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = _ := by
      rw [(summable_geometric_of_lt_one hq0 hq1).tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1]
      simp only [div_eq_mul_inv]

/-- The negative-moment estimate also applies to a nonnegative function. The
real power at zero is handled explicitly, so no atomlessness is needed. -/
theorem lintegral_rpow_neg_le_of_distribution_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    {C s t : ℝ} (hf : Measurable f) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hst : t < s)
    (hf_bounds : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hcount : ∀ u : ℝ, 0 < u →
      μ {x | f x ≤ u} ≤ ENNReal.ofReal (C * u ^ s)) :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ (-t)) ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  classical
  let g : α → ℝ := {x | f x = 0}.piecewise (fun _ => 1) f
  have hg : Measurable g :=
    measurable_const.piecewise (measurableSet_eq_fun hf measurable_const) hf
  have hgb (x : α) : 0 < g x ∧ g x ≤ 1 := by
    by_cases hx : f x = 0
    · simp [g, hx]
    · simpa [g, hx] using
        And.intro (lt_of_le_of_ne (hf_bounds x).1 (Ne.symm hx)) (hf_bounds x).2
  have hfg (x : α) : f x ≤ g x := by
    by_cases hx : f x = 0 <;> simp [g, hx]
  have hkernel (x : α) :
      ENNReal.ofReal ((f x) ^ (-t)) ≤ ENNReal.ofReal ((g x) ^ (-t)) := by
    by_cases hx : f x = 0
    · by_cases ht0 : t = 0
      · simp [ht0]
      · simp [g, hx, Real.zero_rpow (neg_ne_zero.mpr ht0)]
    · simp [g, hx]
  exact (lintegral_mono hkernel).trans
    (lintegral_rpow_neg_le_of_distribution μ g hg hC ht hst hgb (fun u hu =>
      (measure_mono (fun x hx => (hfg x).trans hx)).trans (hcount u hu)))

/-- An all-scale interval cap controls the untruncated Riesz potential. -/
theorem potential_le_of_all_scale_interval_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {C s t : ℝ}
    (hC : 1 ≤ C) (ht : 0 ≤ t) (hst : t < s)
    (hcap : ∀ x u : ℝ, 0 < u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal (|x - y| ^ (-t)) ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  let f : ℝ → ℝ := fun y => min 1 |x - y|
  have hf : Measurable f := measurable_const.min ((measurable_const.sub measurable_id).abs)
  have hfb (y : ℝ) : 0 ≤ f y ∧ f y ≤ 1 :=
    ⟨le_min zero_le_one (abs_nonneg _), min_le_left _ _⟩
  have hcount (u : ℝ) (hu : 0 < u) :
      μ {y | f y ≤ u} ≤ ENNReal.ofReal (C * u ^ s) := by
    by_cases hu1 : 1 ≤ u
    · have hpow : 1 ≤ u ^ s := Real.one_le_rpow hu1 (ht.trans hst.le)
      have hbound : (1 : ℝ) ≤ C * u ^ s := by nlinarith
      exact (measure_mono (subset_univ _)).trans
        (by simpa only [measure_univ, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal hbound)
    · have hsub : {y | f y ≤ u} ⊆ Icc (x - u) (x + u) := by
        intro y hy
        have habs : |x - y| ≤ u := (min_le_iff.mp hy).resolve_left hu1
        obtain ⟨ha, hb⟩ := abs_le.mp habs
        constructor <;> linarith
      exact (measure_mono hsub).trans (hcap x u hu (le_of_not_ge hu1))
  have hkernel (y : ℝ) :
      ENNReal.ofReal (|x - y| ^ (-t)) ≤ ENNReal.ofReal ((f y) ^ (-t)) := by
    by_cases hy : |x - y| ≤ 1
    · simp only [f, min_eq_right hy]
      exact le_rfl
    · simp only [f, min_eq_left (le_of_not_ge hy), Real.one_rpow]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hy) (neg_nonpos.mpr ht))
  exact (lintegral_mono hkernel).trans
    (lintegral_rpow_neg_le_of_distribution_nonneg μ f hf (zero_le_one.trans hC)
      ht hst hfb hcount)

/-- The all-scale Frostman energy estimate in double-integral form. -/
theorem energy_le_of_all_scale_interval_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {C s t : ℝ}
    (hC : 1 ≤ C) (ht : 0 ≤ t) (hst : t < s)
    (hcap : ∀ x u : ℝ, 0 < u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|x - y| ^ (-t)) ∂μ ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  calc _ ≤ ∫⁻ _x, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) ∂μ :=
      lintegral_mono (potential_le_of_all_scale_interval_bound μ hC ht hst hcap)
    _ = _ := by simp

/-- Interval nonconcentration bounds the potential of the truncated Riesz kernel. -/
theorem truncated_potential_le_of_interval_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {r C s t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (ht : 0 ≤ t) (hst : t < s)
    (hcap : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal ((max r |x - y|) ^ (-t)) ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  let f : ℝ → ℝ := fun y => max r (min 1 |x - y|)
  have hf : Measurable f :=
    measurable_const.max (measurable_const.min ((measurable_const.sub measurable_id).abs))
  have hfb (y : ℝ) : 0 < f y ∧ f y ≤ 1 :=
    ⟨hr.trans_le (le_max_left _ _), max_le hr1 (min_le_left _ _)⟩
  have hcount (u : ℝ) (hu : 0 < u) :
      μ {y | f y ≤ u} ≤ ENNReal.ofReal (C * u ^ s) := by
    by_cases hu1 : 1 ≤ u
    · have hpow : 1 ≤ u ^ s := Real.one_le_rpow hu1 (ht.trans hst.le)
      have hbound : (1 : ℝ) ≤ C * u ^ s := by nlinarith
      exact (measure_mono (subset_univ _)).trans
        (by simpa only [measure_univ, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal hbound)
    · by_cases hru : r ≤ u
      · have hsub : {y | f y ≤ u} ⊆ Icc (x - u) (x + u) := by
          intro y hy
          have hmin : min 1 |x - y| ≤ u := (max_le_iff.mp hy).2
          have habs : |x - y| ≤ u :=
            (min_le_iff.mp hmin).resolve_left hu1
          obtain ⟨ha, hb⟩ := abs_le.mp habs
          constructor <;> linarith
        exact (measure_mono hsub).trans (hcap x u hru (le_of_not_ge hu1))
      · have hempty : {y | f y ≤ u} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hru ((le_max_left _ _).trans hy)
        rw [hempty, measure_empty]
        exact bot_le
  have hkernel (y : ℝ) :
      ENNReal.ofReal ((max r |x - y|) ^ (-t)) ≤ ENNReal.ofReal ((f y) ^ (-t)) := by
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
      (hfb y).1 (max_le_max le_rfl (min_le_right _ _)) (neg_nonpos.mpr ht))
  exact (lintegral_mono hkernel).trans
    (lintegral_rpow_neg_le_of_distribution μ f hf (zero_le_one.trans hC)
      ht hst hfb hcount)

/-- The double truncated energy bound has a constant independent of its scale. -/
theorem truncated_energy_le_of_interval_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {r C s t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (ht : 0 ≤ t) (hst : t < s)
    (hcap : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((max r |x - y|) ^ (-t)) ∂μ ∂μ) ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  calc _ ≤ ∫⁻ _x, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) ∂μ :=
      lintegral_mono (truncated_potential_le_of_interval_bound μ hr hr1 hC ht hst hcap)
    _ = _ := by simp

/-- A fixed constant is dominated by an arbitrarily small negative power. -/
theorem exists_scale_absorb_constant (C a : ℝ) (ha : 0 < a) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r < r₀ → C ≤ r ^ (-a) := by
  let K : ℝ := max 1 C
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨min 1 (K ^ (-a⁻¹)), lt_min zero_lt_one (Real.rpow_pos_of_pos hK _),
    min_le_left _ _, ?_⟩
  intro r hr hrr
  have hbound : r ≤ K ^ (-a⁻¹) := (lt_min_iff.mp hrr).2.le
  calc C ≤ K := le_max_right _ _
    _ = (K ^ (-a⁻¹)) ^ (-a) := by
      rw [← Real.rpow_mul hK.le, neg_mul_neg, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ r ^ (-a) := Real.rpow_le_rpow_of_nonpos hr hbound (neg_nonpos.mpr ha.le)

/-- The slack between a Frostman exponent and an energy exponent absorbs the
fixed geometric-annulus constant at all sufficiently small scales. -/
theorem finite_scale_energy_bound {s t ε : ℝ}
    (ht : 0 ≤ t) (hst : t < s) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      (∀ x u : ℝ, r ≤ u → u ≤ 1 →
        μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-(ε / 2)) * u ^ s)) →
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((max r |x - y|) ^ (-t)) ∂μ ∂μ) ≤
        ENNReal.ofReal (r ^ (-ε)) := by
  let A : ℝ := (1 / 2 : ℝ) ^ (-t) / (1 - (1 / 2 : ℝ) ^ (s - t))
  obtain ⟨r₀, hr₀, hr₀1, hA⟩ := exists_scale_absorb_constant A (ε / 2) (by linarith)
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  intro r hr hrr μ hμ hcap
  let : IsProbabilityMeasure μ := hμ
  have hr1 : r ≤ 1 := hrr.le.trans hr₀1
  have hC : 1 ≤ r ^ (-(ε / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have henergy := truncated_energy_le_of_interval_bound μ hr hr1 hC ht hst hcap
  refine henergy.trans (ENNReal.ofReal_le_ofReal ?_)
  calc r ^ (-(ε / 2)) * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t)) = r ^ (-(ε / 2)) * A := by dsimp [A]; ring
    _ ≤ r ^ (-(ε / 2)) * r ^ (-(ε / 2)) :=
      mul_le_mul_of_nonneg_left (hA r hr hrr) (Real.rpow_nonneg hr.le _)
    _ = r ^ (-ε) := by rw [← Real.rpow_add hr]; congr 1; ring

/-- Equal energy exponents strictly below the Frostman exponent can have total
sum larger than one, by increasing the number of factors. -/
theorem exists_energy_exponents {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t < s ∧ 1 < (n : ℝ) * t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 2 (2 / s))
  have hn2 : (2 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnprod : 2 < (n : ℝ) * s :=
    (div_lt_iff₀ hs).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  refine ⟨n, by exact_mod_cast hn2.le, s / 2, by linarith, by linarith,
    by linarith, ?_⟩
  nlinarith

end Submission.Obl.k4_oss_flat_decay
