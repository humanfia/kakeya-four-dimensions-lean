import Mathlib

open Filter Set
open scoped Topology

namespace Submission.Obl.k4_oss_dyadic_reduction

lemma tendsto_pos_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => r ^ a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa only [Real.zero_rpow ha.ne'] using (Real.continuous_rpow_const ha.le).tendsto 0

lemma eventually_small_power (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), C * r ^ a ≤ 1 := by
  have hlim : Tendsto (fun r : ℝ => C * r ^ a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul (tendsto_pos_rpow_zero ha)
  exact (hlim.eventually_le_const (by norm_num)).filter_mono nhdsWithin_le_nhds

lemma eventually_absorb_power (C : ℝ) {a b : ℝ} (hab : b < a) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), C * r ^ a ≤ (r / 2) ^ b := by
  filter_upwards [eventually_small_power (C * (2 : ℝ) ^ b) (sub_pos.mpr hab),
    self_mem_nhdsWithin] with r hh hr
  have hr : 0 < r := hr
  rw [Real.div_rpow hr.le (by norm_num), le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) b)]
  calc
    C * r ^ a * (2 : ℝ) ^ b =
        (C * (2 : ℝ) ^ b * r ^ (a - b)) * r ^ b := by
      rw [mul_assoc (C * (2 : ℝ) ^ b), ← Real.rpow_add hr]
      have he : a - b + b = a := by ring
      rw [he]
      ring
    _ ≤ 1 * r ^ b := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hr.le b)
    _ = r ^ b := one_mul _

/-- All numerical choices needed by the finite-mesh localization. -/
lemma exists_mesh_parameters (n : ℕ) {s ε t δ₀ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 < ε) (ht : 0 < t) (hδ₀ : 0 < δ₀) :
    ∃ ε₀ τ r₀ : ℝ, 0 < ε₀ ∧ 0 < τ ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∃ (N : ℕ) (η D : ℝ),
        0 < N ∧ r ≤ 1 / (N : ℝ) ∧ 0 < η ∧ 0 < D ∧ D < δ₀ ∧
        r * (N : ℝ) ^ n ≤ D ∧
        η⁻¹ * r ^ (-ε₀) ≤ D ^ (-ε) ∧
        D ^ t + n * (r ^ (-ε₀) * (1 / (N : ℝ)) ^ s + 2 * N * η) ≤ (r / 2) ^ τ := by
  let q : ℝ := min (1 / (8 * ((n : ℝ) + 1))) (ε / 8)
  have hq : 0 < q := lt_min (by positivity) (by positivity)
  have hqN : q * (8 * ((n : ℝ) + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hqε : q ≤ ε / 8 := min_le_right _ _
  have hq1 : q < 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hqn : (n : ℝ) * q < 1 / 2 := by nlinarith
  let ε₀ : ℝ := q * s / 2
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀q : ε₀ ≤ q / 2 := by dsimp [ε₀]; nlinarith
  have hcoeff : 2 * q + ε₀ ≤ ε / 2 := by nlinarith
  let α : ℝ := min (t / 2) (min ε₀ q)
  have hα : 0 < α := lt_min (by positivity) (lt_min hε₀ hq)
  have hαt : α ≤ t / 2 := min_le_left _ _
  have hαε : α ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hαq : α ≤ q := (min_le_right _ _).trans (min_le_right _ _)
  let τ : ℝ := α / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτa : τ < α := by dsimp [τ]; linarith
  have hpowδ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ^ (1 / 2 : ℝ) < δ₀ :=
    ((tendsto_pos_rpow_zero (by norm_num : (0 : ℝ) < 1 / 2)).eventually_lt_const hδ₀).filter_mono
      nhdsWithin_le_nhds
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      r < 1 ∧ 2 * r ^ (1 - q) ≤ 1 ∧
      (2 : ℝ) ^ n * r ^ (1 / 2 - (n : ℝ) * q) ≤ 1 ∧
      r ^ (1 / 2 : ℝ) < δ₀ ∧ (1 + 5 * (n : ℝ)) * r ^ α ≤ (r / 2) ^ τ := by
    filter_upwards [(show ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), r < 1 from
        Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds,
      eventually_small_power 2 (sub_pos.mpr hq1),
      eventually_small_power ((2 : ℝ) ^ n) (sub_pos.mpr hqn), hpowδ,
      eventually_absorb_power (1 + 5 * (n : ℝ)) hτa] with r hr h1 h2 h3 h4
    exact ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨r₀, hr₀, hrsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨ε₀, τ, r₀, hε₀, hτ, hr₀, ?_⟩
  intro r hr hrr₀
  obtain ⟨hr1, hsmall1, hsmallN, hsmallδ, habsorb⟩ := hrsmall ⟨hr, hrr₀⟩
  let N : ℕ := ⌈r ^ (-q)⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hr _)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNlo : r ^ (-q) ≤ (N : ℝ) := Nat.le_ceil _
  have hrq1 : 1 ≤ r ^ (-q) := by
    calc
      1 = r ^ (0 : ℝ) := (Real.rpow_zero r).symm
      _ ≤ r ^ (-q) := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith)
  have hNup : (N : ℝ) ≤ 2 * r ^ (-q) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hr.le (-q))
    dsimp [N]
    linarith
  have hrN : r ≤ 1 / (N : ℝ) := by
    apply (le_div_iff₀ hNR).mpr
    calc
      r * N ≤ r * (2 * r ^ (-q)) := mul_le_mul_of_nonneg_left hNup hr.le
      _ = 2 * r ^ (1 - q) := by
        rw [show 1 - q = 1 + (-q) by ring, Real.rpow_add hr, Real.rpow_one]
        ring
      _ ≤ 1 := hsmall1
  have hbq : 1 / (N : ℝ) ≤ r ^ q := by
    calc
      1 / (N : ℝ) ≤ 1 / r ^ (-q) := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hr _) hNlo
      _ = r ^ q := by rw [Real.rpow_neg hr.le, one_div, inv_inv]
  let η : ℝ := r ^ (2 * q)
  let D : ℝ := r ^ (1 / 2 : ℝ)
  have hη : 0 < η := Real.rpow_pos_of_pos hr _
  have hD : 0 < D := Real.rpow_pos_of_pos hr _
  have hND : r * (N : ℝ) ^ n ≤ D := by
    calc
      r * (N : ℝ) ^ n ≤ r * (2 * r ^ (-q)) ^ n := by gcongr
      _ = (2 : ℝ) ^ n * r ^ (1 - (n : ℝ) * q) := by
        rw [mul_pow, show 1 - (n : ℝ) * q = 1 + (-q) * (n : ℝ) by ring,
          Real.rpow_add hr, Real.rpow_one, Real.rpow_mul hr.le, Real.rpow_natCast]
        ring
      _ = ((2 : ℝ) ^ n * r ^ (1 / 2 - (n : ℝ) * q)) * r ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 2
        ring
      _ ≤ 1 * r ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsmallN (Real.rpow_nonneg hr.le _)
      _ = D := one_mul _
  have hcoef : η⁻¹ * r ^ (-ε₀) ≤ D ^ (-ε) := by
    dsimp [η, D]
    rw [← Real.rpow_neg hr.le, ← Real.rpow_add hr, ← Real.rpow_mul hr.le]
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1.le
    linarith
  have hdeep : r ^ (-ε₀) * (1 / (N : ℝ)) ^ s ≤ r ^ ε₀ := by
    calc
      _ ≤ r ^ (-ε₀) * (r ^ q) ^ s := by gcongr
      _ = r ^ ε₀ := by
        rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
        congr 1
        dsimp [ε₀]
        ring
  have hlight : 2 * (N : ℝ) * η ≤ 4 * r ^ q := by
    calc
      _ ≤ 2 * (2 * r ^ (-q)) * r ^ (2 * q) := by dsimp [η]; gcongr
      _ = 4 * r ^ q := by
        rw [show 2 * (2 * r ^ (-q)) * r ^ (2 * q) =
          4 * (r ^ (-q) * r ^ (2 * q)) by ring,
          ← Real.rpow_add hr, show -q + 2 * q = q by ring]
  have hfinal : D ^ t + n * (r ^ (-ε₀) * (1 / (N : ℝ)) ^ s + 2 * N * η) ≤ (r / 2) ^ τ := by
    have hDt : D ^ t ≤ r ^ α := by
      dsimp [D]
      rw [← Real.rpow_mul hr.le]
      exact Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith [hαt])
    have hdeepα : r ^ (-ε₀) * (1 / (N : ℝ)) ^ s ≤ r ^ α :=
      hdeep.trans (Real.rpow_le_rpow_of_exponent_ge hr hr1.le hαε)
    have hlightα : 2 * (N : ℝ) * η ≤ 4 * r ^ α :=
      hlight.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hr hr1.le hαq) (by norm_num))
    calc
      _ ≤ r ^ α + n * (r ^ α + 4 * r ^ α) := by gcongr
      _ = (1 + 5 * (n : ℝ)) * r ^ α := by ring
      _ ≤ _ := habsorb
  exact ⟨N, η, D, hN, hrN, hη, hD, hsmallδ, hND, hcoef, hfinal⟩

end Submission.Obl.k4_oss_dyadic_reduction
