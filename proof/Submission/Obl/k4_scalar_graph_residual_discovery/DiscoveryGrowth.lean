/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryGrowth.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryGrowth

open Filter
open scoped BigOperators ENNReal
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem subpower_one {N : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) :
    Subpower N (fun _ => 1) :=
  ⟨fun _ => le_rfl, fun _ε hε =>
    Eventually.of_forall (fun k => Real.one_le_rpow (hN k) hε.le)⟩

/-- Combine original subpower budgets using the accepted horizon API. -/
theorem subpower_mul {N P Q : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hP : Subpower N P) (hQ : Subpower N Q) :
    Subpower N (fun k => P k * Q k) := by
  refine ⟨fun k => ?_, ?_⟩
  · have hp := hP.1 k
    have hq := hQ.1 k
    nlinarith only [hp, hq, mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
  · exact Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul
      (fun k => zero_lt_one.trans_le (hN k))
      (fun k => zero_le_one.trans (hP.1 k)) (fun k => zero_le_one.trans (hQ.1 k)) hP.2 hQ.2

theorem subpower_finset_prod {ι : Type*} [DecidableEq ι] {N : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (s : Finset ι) (F : ι → ℕ → ℝ)
    (hF : ∀ i ∈ s, Subpower N (F i)) :
    Subpower N (fun k => ∏ i ∈ s, F i k) := by
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa only [Finset.prod_empty] using subpower_one hN
  · intro i s hi ih hF
    simpa only [Finset.prod_insert hi] using
      subpower_mul hN (hF i (Finset.mem_insert_self i s))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- Eventual domination by one fixed polynomial budget suffices. -/
theorem subpower_of_polynomial_bound {N H F : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hH : Subpower N H)
    {A : ℝ} (hA : 1 ≤ A) (p : ℕ) (hF : ∀ k, 1 ≤ F k)
    (hbound : ∀ᶠ k in atTop, F k ≤ A * H k ^ p) : Subpower N F := by
  refine ⟨hF, fun ε hε => ?_⟩
  filter_upwards [hbound, (subpower_polynomial hN hNt hH hA p).2 ε hε] with k hk hb
  exact hk.trans hb

theorem subpower_nat_ceil {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hH : Subpower N H) :
    Subpower N (fun k => (⌈H k⌉₊ : ℝ)) := by
  refine subpower_of_polynomial_bound hN hNt hH (A := 2) (by norm_num) 1
    (fun k => (hH.1 k).trans (Nat.le_ceil _)) (Eventually.of_forall fun k => ?_)
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ H k by linarith [hH.1 k])).le
  simp only [pow_one]
  linarith [hH.1 k]

/-- The literal first whole-state row-selection cost is subpower for every
fixed number of levels, including `C₁ * J₁ + 1`. -/
theorem subpower_first_row_factor {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hH : Subpower N H) (L : ℕ) :
    Subpower N (fun k => ((4 : ℝ) ^ 3 * (8 * (⌈(2 * H k + 2) ^ 2⌉₊ : ℝ))) ^ L) := by
  have hquad : Subpower N (fun k => (2 * H k + 2) ^ 2) := by
    refine subpower_of_polynomial_bound hN hNt hH (A := 16) (by norm_num) 2
      (fun k => ?_) (Eventually.of_forall fun k => ?_)
    · nlinarith only [hH.1 k, sq_nonneg (H k - 1)]
    · have hp : 0 ≤ (H k - 1) * (3 * H k + 1) :=
        mul_nonneg (sub_nonneg.mpr (hH.1 k)) (by linarith [hH.1 k])
      nlinarith only [hp]
  have hceil := subpower_nat_ceil hN hNt hquad
  have hscaled : Subpower N (fun k => 512 * (⌈(2 * H k + 2) ^ 2⌉₊ : ℝ)) := by
    simpa only [pow_one] using
      subpower_polynomial hN hNt hceil (A := 512) (by norm_num) 1
  have hbase : Subpower N (fun k => (4 : ℝ) ^ 3 * (8 * (⌈(2 * H k + 2) ^ 2⌉₊ : ℝ))) := by
    have heq : (fun k => (4 : ℝ) ^ 3 * (8 * (⌈(2 * H k + 2) ^ 2⌉₊ : ℝ))) =
        (fun k => 512 * (⌈(2 * H k + 2) ^ 2⌉₊ : ℝ)) := by
      funext k
      ring
    rw [heq]
    exact hscaled
  simpa only [one_mul] using subpower_polynomial hN hNt hbase (A := 1) (by norm_num) L

/-- Use the accepted exponent-gap estimate for every fixed polynomial cost. -/
theorem eventually_monomial_lt {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hH : Subpower N H)
    (p : ℕ) {a b A : ℝ} (hab : a < b) (hA : 0 ≤ A) :
    ∀ᶠ k in atTop, A * H k ^ p * N k ^ a < N k ^ b :=
  Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hH.1 hH.2 p hab hA

/-- A fixed power saving pays a subpower loss against the original source floor. -/
theorem eventually_loss_lt_half_floor {N P Q : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (hQ : Subpower N Q) {ω : ℝ} (hω : 0 < ω) :
    ∀ᶠ k in atTop, Q k * N k ^ (-ω) < (2 * P k)⁻¹ := by
  have hg := eventually_monomial_lt hN hNt (subpower_mul hN hP hQ) 1
    (a := -ω) (b := 0) (by linarith) (A := 2) (by norm_num)
  filter_upwards [hg] with k hk
  simp only [pow_one, Real.rpow_zero] at hk
  rw [← one_div, lt_div_iff₀ (show 0 < 2 * P k by linarith [hP.1 k])]
  nlinarith only [hk]

theorem eventually_retained_floor {N P Q source retained : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (hQ : Subpower N Q) {ω : ℝ} (hω : 0 < ω)
    (hsource : ∀ᶠ k in atTop, (P k)⁻¹ ≤ source k)
    (hprune : ∀ᶠ k in atTop, source k ≤ retained k + Q k * N k ^ (-ω)) :
    ∀ᶠ k in atTop, (2 * P k)⁻¹ ≤ retained k := by
  filter_upwards [eventually_loss_lt_half_floor hN hNt hP hQ hω, hsource, hprune]
    with k hloss hs hp
  have hid : (P k)⁻¹ = 2 * (2 * P k)⁻¹ := by
    field_simp [ne_of_gt (show 0 < P k by linarith [hP.1 k])]
  rw [hid] at hs
  linarith

/-- The same original floor survives pruning directly in extended measure values. -/
theorem eventually_retained_floor_ennreal {N P Q : ℕ → ℝ}
    {source retained : ℕ → ℝ≥0∞}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (hQ : Subpower N Q) {ω : ℝ} (hω : 0 < ω)
    (hsource : ∀ᶠ k in atTop, ENNReal.ofReal ((P k)⁻¹) ≤ source k)
    (hprune : ∀ᶠ k in atTop,
      source k ≤ retained k + ENNReal.ofReal (Q k * N k ^ (-ω))) :
    ∀ᶠ k in atTop, ENNReal.ofReal ((2 * P k)⁻¹) ≤ retained k := by
  filter_upwards [eventually_loss_lt_half_floor hN hNt hP hQ hω, hsource, hprune]
    with k hloss hs hp
  by_cases ht : retained k = ⊤
  · simp only [ht, le_top]
  · have hPpos : 0 < P k := by linarith [hP.1 k]
    have hlossnonneg : 0 ≤ Q k * N k ^ (-ω) :=
      mul_nonneg (zero_le_one.trans (hQ.1 k))
        (Real.rpow_nonneg (zero_le_one.trans (hN k)) _)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ht, ENNReal.ofReal_ne_top⟩)
      (hs.trans hp)
    rw [ENNReal.toReal_add ht ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hPpos.le),
      ENNReal.toReal_ofReal hlossnonneg] at hreal
    have hid : (P k)⁻¹ = 2 * (2 * P k)⁻¹ := by field_simp [hPpos.ne']
    have hhalf : (2 * P k)⁻¹ ≤ (retained k).toReal := by
      rw [hid] at hreal
      linarith
    rw [← ENNReal.ofReal_toReal ht]
    exact ENNReal.ofReal_le_ofReal hhalf

/-- A fixed number of selection stages consumes its displayed power exponent. -/
theorem eventually_scaled_pow_lt {N P : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hP : Subpower N P)
    (L : ℕ) {a b : ℝ} (hab : a * (L : ℝ) < b) :
    ∀ᶠ k in atTop, (P k * N k ^ a) ^ L < N k ^ b := by
  filter_upwards [eventually_monomial_lt hN hNt hP L hab (A := 1) (by norm_num)] with k hk
  have heq : (N k ^ a) ^ L = N k ^ (a * (L : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans (hN k))]
  simpa only [mul_pow, heq, one_mul] using hk

theorem eventually_nat_ceil_le_scaled {N P F : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hP : ∀ k, 1 ≤ P k)
    {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ᶠ k in atTop, 0 ≤ F k)
    (hbound : ∀ᶠ k in atTop, F k ≤ P k * N k ^ a) :
    ∀ᶠ k in atTop, (⌈F k⌉₊ : ℝ) ≤ (2 * P k) * N k ^ a := by
  filter_upwards [hF, hbound] with k hk hb
  have hpower : 1 ≤ N k ^ a := Real.one_le_rpow (hN k) ha
  have hbudget : 1 ≤ P k * N k ^ a := by
    nlinarith only [hP k, hpower,
      mul_nonneg (sub_nonneg.mpr (hP k)) (sub_nonneg.mpr hpower)]
  have hc := (Nat.ceil_lt_add_one hk).le
  nlinarith only [hc, hb, hbudget]

/-- Uniform list bounds control the actual product of the finite selection costs. -/
theorem eventually_selection_cost_lt {ι : Type*} [DecidableEq ι]
    {N P : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (s : Finset ι) (K : ι → ℕ → ℕ)
    {C a b : ℝ} (hC : 1 ≤ C) (hab : a * (s.card : ℝ) < b)
    (hbound : ∀ i ∈ s, ∀ᶠ k in atTop, (K i k : ℝ) ≤ P k * N k ^ a) :
    ∀ᶠ k in atTop, (∏ i ∈ s, C * (K i k : ℝ)) < N k ^ b := by
  have hscaled : Subpower N (fun k => C * P k) := by
    simpa only [pow_one] using subpower_polynomial hN hNt hP hC 1
  filter_upwards [(Filter.eventually_all_finset s).mpr hbound,
    eventually_scaled_pow_lt hN hNt hscaled s.card hab] with k hk hp
  apply lt_of_le_of_lt _ hp
  calc
    (∏ i ∈ s, C * (K i k : ℝ)) ≤ ∏ _i ∈ s, (C * P k) * N k ^ a := by
      apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (zero_le_one.trans hC) (Nat.cast_nonneg _))
      intro i hi
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hk i hi) (zero_le_one.trans hC)
    _ = ((C * P k) * N k ^ a) ^ s.card := by rw [Finset.prod_const]

/-- Round real list bounds and absorb their entire fixed finite product. -/
theorem eventually_ceil_selection_cost_lt {ι : Type*} [DecidableEq ι]
    {N P : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (s : Finset ι) (F : ι → ℕ → ℝ)
    {C a b : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) (hab : a * (s.card : ℝ) < b)
    (hF : ∀ i ∈ s, ∀ᶠ k in atTop, 0 ≤ F i k)
    (hbound : ∀ i ∈ s, ∀ᶠ k in atTop, F i k ≤ P k * N k ^ a) :
    ∀ᶠ k in atTop, (∏ i ∈ s, C * (⌈F i k⌉₊ : ℝ)) < N k ^ b := by
  have htwo : Subpower N (fun k => 2 * P k) := by
    simpa only [pow_one] using subpower_polynomial hN hNt hP (A := 2) (by norm_num) 1
  exact eventually_selection_cost_lt hN hNt htwo s (fun i k => ⌈F i k⌉₊) hC hab
    (fun i hi => eventually_nat_ceil_le_scaled hN hP.1 ha (hF i hi) (hbound i hi))

/-- The rounded selection cost in the extended measure units used by common choice. -/
theorem eventually_ceil_selection_cost_le_ennreal {ι : Type*} [DecidableEq ι]
    {N P : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : Subpower N P) (s : Finset ι) (F : ι → ℕ → ℝ)
    {C : ℕ} {a b : ℝ} (hC : 1 ≤ C) (ha : 0 ≤ a) (hab : a * (s.card : ℝ) < b)
    (hF : ∀ i ∈ s, ∀ᶠ k in atTop, 0 ≤ F i k)
    (hbound : ∀ i ∈ s, ∀ᶠ k in atTop, F i k ≤ P k * N k ^ a) :
    ∀ᶠ k in atTop, (∏ i ∈ s, (C : ℝ≥0∞) * (⌈F i k⌉₊ : ℝ≥0∞)) ≤
      ENNReal.ofReal (N k ^ b) := by
  filter_upwards [eventually_ceil_selection_cost_lt hN hNt hP s F
    (C := (C : ℝ)) (by exact_mod_cast hC) ha hab hF hbound] with k hk
  have hle := ENNReal.ofReal_le_ofReal hk.le
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    mul_nonneg (Nat.cast_nonneg C) (Nat.cast_nonneg _))] at hle
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg C), ENNReal.ofReal_natCast] using hle

end Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryGrowth
