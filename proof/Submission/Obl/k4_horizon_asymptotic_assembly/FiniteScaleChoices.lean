/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/FiniteScaleChoices.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Submission.Obl.k4_horizon_asymptotic_assembly.FiniteScaleNumerics
import Submission.Obl.k4_horizon_asymptotic_assembly.Defs
import Submission.Obl.k4_profile_density_bounds.Common

/-! Concrete dyadic blocks, integer meshes and original mass retention for the
finite-to-asymptotic atlas conversion. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace Submission.Obl.k4_horizon_asymptotic_assembly

noncomputable def initialBlockDepth (N L : ℝ) : ℕ := ⌊L * Real.log N / Real.log 2⌋₊ + 3

theorem initialBlockDepth_scale {N L : ℝ} (hN : 2 ≤ N) (hL : 0 ≤ L) :
    ((2 : ℝ) ^ initialBlockDepth N L)⁻¹ = Outer.dl N L / 8 := by
  have hx : 0 ≤ L * Real.log N / Real.log 2 := by
    exact div_nonneg (mul_nonneg hL (Real.log_nonneg (by linarith))) (Real.log_pos (by norm_num)).le
  unfold initialBlockDepth Outer.dl
  rw [← Int.natCast_floor_eq_floor hx, zpow_neg, zpow_natCast, pow_add]
  norm_num
  ring

theorem initialBlockDepth_bounds {N L : ℝ} (hN : 2 ≤ N) (hL : 0 ≤ L) :
    0 < Outer.dl N L ∧ Outer.dl N L ≤ 1 ∧
    N ^ (-L) / 8 ≤ ((2 : ℝ) ^ initialBlockDepth N L)⁻¹ ∧
    (2 : ℝ) ^ initialBlockDepth N L ≤ 8 * N ^ L := by
  have hn : 0 < N := by linarith
  have hp : 0 < Outer.dl N L := Submission.Obl.k4_profile_density_bounds.width_pos N L
  have hb := Submission.Obl.k4_profile_density_bounds.width_bounds hn L
  change N ^ (-L) ≤ Outer.dl N L ∧ _ at hb
  have hx : 0 ≤ L * Real.log N / Real.log 2 := by
    exact div_nonneg (mul_nonneg hL (Real.log_nonneg (by linarith))) (Real.log_pos (by norm_num)).le
  have ha1 : Outer.dl N L ≤ 1 := by
    change (2 : ℝ) ^ (-⌊L * Real.log N / Real.log 2⌋ : ℤ) ≤ 1
    exact zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (Int.floor_nonneg.mpr hx))
  refine ⟨hp, ha1, ?_, ?_⟩
  · rw [initialBlockDepth_scale hN hL]
    linarith [hb.1]
  · have ht : 0 < (2 : ℝ) ^ initialBlockDepth N L := by positivity
    have heq := initialBlockDepth_scale hN hL
    have hlow : N ^ (-L) / 8 ≤ ((2 : ℝ) ^ initialBlockDepth N L)⁻¹ := by
      rw [heq]
      linarith [hb.1]
    have hh := inv_anti₀ (by positivity : 0 < N ^ (-L) / 8) hlow
    rw [inv_inv, inv_div, Real.rpow_neg hn.le, div_inv_eq_mul] at hh
    exact hh

theorem initial_integer_mesh_bounds {N : ℝ} {J : ℕ} (hN : 2 ≤ N) (hJ : 1 ≤ J) :
    2 ≤ ⌈N ^ J⌉₊ ∧ N ^ J ≤ (⌈N ^ J⌉₊ : ℝ) ∧
    (⌈N ^ J⌉₊ : ℝ) ≤ N ^ (J + 1) := by
  have hN1 : 1 ≤ N := by linarith
  have hpow : N ≤ N ^ J := by simpa only [pow_one] using pow_le_pow_right₀ hN1 hJ
  have hlo := Nat.le_ceil (N ^ J)
  refine ⟨?_, hlo, ?_⟩
  · exact_mod_cast hN.trans (hpow.trans hlo)
  · have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ N ^ J)).le
    have hp1 : 1 ≤ N ^ J := one_le_pow₀ hN1
    calc
      _ ≤ N ^ J + 1 := hceil
      _ ≤ N ^ J * N := by nlinarith
      _ = _ := (pow_succ N J).symm

theorem eventually_initial_slack_dominates {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, 256 * (K k + 2) ≤ N k ^ ε := by
  have hh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 hε (show (0 : ℝ) ≤ 768 by norm_num)
  filter_upwards [hh] with k hk
  simp only [Real.rpow_zero, pow_one, mul_one] at hk
  nlinarith [hK k]

/-- The residual allowance leaves half of the original `1/K` mass. -/
theorem initial_mass_retention {K : ℝ} (hK : 0 < K) {m a b : ENNReal}
    (hm : m ≠ ⊤) (hstart : ENNReal.ofReal K⁻¹ ≤ m)
    (hbad : b ≤ ENNReal.ofReal ((16 * K)⁻¹))
    {e : ℝ} (he : e ≤ 1 / 4)
    (hres : m ≤ a + b + ENNReal.ofReal ((16 * K)⁻¹) + ENNReal.ofReal e * m) :
    ENNReal.ofReal ((2 * K)⁻¹) ≤ a := by
  by_cases ha : a = ⊤
  · simp [ha]
  have hres' : m ≤ a + ENNReal.ofReal ((16 * K)⁻¹) +
      ENNReal.ofReal ((16 * K)⁻¹) + ENNReal.ofReal (1 / 4) * m :=
    hres.trans (add_le_add (add_le_add (add_le_add le_rfl hbad) le_rfl)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl))
  have htop : a + ENNReal.ofReal ((16 * K)⁻¹) + ENNReal.ofReal ((16 * K)⁻¹) +
      ENNReal.ofReal (1 / 4) * m ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono htop hres'
  have hs := ENNReal.toReal_mono hm hstart
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add ha ENNReal.ofReal_ne_top, ENNReal.toReal_mul] at hr
  have h16pos : 0 < 16 * K := mul_pos (by norm_num) hK
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hK.le),
    ENNReal.toReal_ofReal (inv_nonneg.mpr h16pos.le),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hr hs
  have hreal : (2 * K)⁻¹ ≤ a.toReal := by
    have h16 : (16 * K)⁻¹ = K⁻¹ / 16 := by field_simp
    have h2 : (2 * K)⁻¹ = K⁻¹ / 2 := by field_simp
    rw [h16] at hr
    rw [h2]
    linarith [inv_pos.mpr hK]
  calc
    _ ≤ ENNReal.ofReal a.toReal := ENNReal.ofReal_le_ofReal hreal
    _ = a := ENNReal.ofReal_toReal ha

end Submission.Obl.k4_horizon_asymptotic_assembly
