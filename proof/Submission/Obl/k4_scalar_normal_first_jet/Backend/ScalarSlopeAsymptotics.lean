/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarSlopeAsymptotics.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarSlopeAsymptotics.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSlopeBudgets
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

/-! Subpower losses in the prepared residual-slope argument. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Filter
open scoped Topology
open Submission.Obl.k4_discrete_of_terminal_charts

theorem subpower_polynomial_decay_eventually (N K : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 0 ≤ K k) (hsub : SubpowerBound N K)
    (m : ℕ) {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) :
    ∀ᶠ k in atTop, C * K k ^ m * N k ^ (-a) < b := by
  have hpow := subpower_pow hN hK hsub m (a / 2) (by positivity)
  have hlim : Tendsto (fun k => C * N k ^ (-(a / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by positivity : 0 < a / 2)).comp hNt).const_mul C
  filter_upwards [hpow, hlim.eventually (gt_mem_nhds hb)] with k hk hsmall
  have hN0 : 0 ≤ N k := zero_le_one.trans (hN k)
  calc
    C * K k ^ m * N k ^ (-a) ≤ C * N k ^ (a / 2) * N k ^ (-a) := by
      gcongr
    _ = C * N k ^ (-(a / 2)) := by
      rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le (hN k))]
      congr 2
      ring
    _ < b := hsmall

theorem residual_slope_budgets_eventually (N K : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d ε : ℝ} (ha : 0 < a) (hd : d < 1) (hε : 0 < ε) (j : ℝ) :
    ∀ᶠ k in atTop,
      let p := N k ^ (-a)
      let τ := N k ^ (-ε / 4)
      let η := N k ^ (-ε)
      let γ := (1 - d) / 4
      τ * K k + (p ^ j * τ) * (K k * p ^ (-j)) ≤ (K k)⁻¹ / 2 ∧
      (3 * (K k * ((2 * K k) / p) ^ d)) *
        (((η / τ) / (p ^ j * τ) * (K k * p ^ (j + d))) * K k +
          (2 * (p + 2 * (K k * p)) / (p ^ γ)) * K k ^ 2) < ((K k)⁻¹ / 2) ^ 2 := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hdecay₀ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 2
    (a := ε / 4) (b := 1) (C := 4) (by positivity) (by norm_num) (by norm_num)
  have hdecay₁ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 6
    (a := ε / 2) (b := 1 / 8) (C := 6) (by positivity) (by norm_num) (by norm_num)
  have hrate : 0 < a * (1 - d - (1 - d) / 4) :=
    mul_pos ha (by linarith)
  have hdecay₂ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 7
    (a := a * (1 - d - (1 - d) / 4)) (b := 1 / 8) (C := 36) hrate (by norm_num) (by norm_num)
  filter_upwards [hdecay₀, hdecay₁, hdecay₂] with k hsmall₀ hsmall₁ hsmall₂
  dsimp only
  let p := N k ^ (-a)
  let τ := N k ^ (-ε / 4)
  let η := N k ^ (-ε)
  let γ := (1 - d) / 4
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hNpos _).le
  have hητ : η / τ ^ 2 = N k ^ (-ε / 2) := by
    dsimp [η, τ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_sub hNpos]
    congr 1
    ring
  have hpRate : p ^ (1 - d - γ) = N k ^ (-(a * (1 - d - (1 - d) / 4))) := by
    dsimp [p, γ]
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hτsmall : 4 * K k ^ 2 * τ < 1 := by simpa only [τ, neg_div] using hsmall₀
  constructor
  · calc
      τ * K k + (p ^ j * τ) * (K k * p ^ (-j)) ≤ 2 * K k * τ :=
        scalar_slope_pruning_cost hp hKpos.le hτ.le le_rfl le_rfl
      _ ≤ (K k)⁻¹ / 2 := by
        rw [inv_eq_one_div, div_div]
        apply (le_div_iff₀ (by positivity : 0 < K k * 2)).mpr
        nlinarith only [hτsmall.le]
  · have hMsmall :
        (6 * K k ^ 4 * η / τ ^ 2 + 36 * K k ^ 5 * p ^ (1 - d - γ)) * K k ^ 2 < 1 / 4 := by
      calc
        _ = 6 * K k ^ 6 * (η / τ ^ 2) + 36 * K k ^ 7 * p ^ (1 - d - γ) := by ring
        _ = 6 * K k ^ 6 * N k ^ (-ε / 2) +
            36 * K k ^ 7 * N k ^ (-(a * (1 - d - (1 - d) / 4))) := by rw [hητ, hpRate]
        _ < 1 / 4 := by
          have hsmall₁' : 6 * K k ^ 6 * N k ^ (-ε / 2) < 1 / 8 := by
            simpa only [neg_div] using hsmall₁
          linarith
    have hR : ((K k)⁻¹ / 2) ^ 2 * K k ^ 2 = 1 / 4 := by
      field_simp
      norm_num
    have hbound : 6 * K k ^ 4 * η / τ ^ 2 + 36 * K k ^ 5 * p ^ (1 - d - γ) < ((K k)⁻¹ / 2) ^ 2 := by
      apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hKpos)).mp
      simpa only [mul_comm] using hMsmall.trans_eq hR.symm
    exact (scalar_slope_collision_cost hp (hK k) hτ hη hd.le).trans_lt hbound

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
