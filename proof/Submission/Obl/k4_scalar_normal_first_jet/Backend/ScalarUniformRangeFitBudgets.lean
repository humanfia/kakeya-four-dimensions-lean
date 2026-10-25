/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformRangeFitBudgets.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformRangeFitBudgets.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformFitBudgets

/-! One threshold for every scalar resolution in a fixed power range. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Filter
open Submission.Obl.k4_discrete_of_terminal_charts

theorem scalar_local_fit_budgets_between_powers (N K : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d σ ε η p₀ τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd : d ≤ 1) (hσ : 0 < σ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hp₀ : 0 < p₀) (hτ : b * ε < τ) :
    ∀ᶠ k in atTop, ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      ScalarLocalFitBudget p (K k) d σ ε η p₀ (N k ^ (-τ)) := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hτa : a * ε < τ := (mul_le_mul_of_nonneg_right hab hε.le).trans_lt hτ
  have hfixed := scalar_local_fit_budgets_eventually N K hN hNt hK hsub ha hd hσ hε1 hη hp₀ hτa
  have hdensity := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 15
    (a := a * η) (b := 1) (C := 11000000000) (mul_pos ha hη) (by norm_num) (by norm_num)
  have hlength := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 14
    (a := τ - b * ε) (b := 1) (C := 11426400) (sub_pos.mpr hτ) (by norm_num) (by norm_num)
  filter_upwards [hfixed, hdensity, hlength] with k hk hdensity hlength
  intro p hlow hhigh
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hp : 0 < p := (Real.rpow_pos_of_pos hNpos (-b)).trans_le hlow
  have hp1 : p ≤ 1 := hhigh.trans hk.unit
  have hneg : (N k ^ (-a)) ^ (-η) ≤ p ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hp hhigh (by linarith)
  have hpη : (N k ^ (-a)) ^ η = N k ^ (-(a * η)) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hsmall : 11000000000 * K k ^ 15 * p ^ η ≤ 1 := by
    calc
      _ ≤ 11000000000 * K k ^ 15 * (N k ^ (-a)) ^ η :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hhigh hη.le) (by positivity)
      _ ≤ 1 := by rw [hpη]; exact hdensity.le
  have hlen : N k ^ (-τ) ≤ p ^ ε / (11426400 * K k ^ 14) := by
    have hpε : (N k ^ (-b)) ^ ε = N k ^ (-(b * ε)) := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    have hbase : N k ^ (-τ) ≤ (N k ^ (-b)) ^ ε / (11426400 * K k ^ 14) := by
      apply (le_div_iff₀ (by positivity : 0 < 11426400 * K k ^ 14)).mpr
      rw [hpε]
      have hh := mul_le_mul_of_nonneg_right hlength.le (Real.rpow_nonneg hNpos.le (-(b * ε)))
      rw [mul_assoc, ← Real.rpow_add hNpos,
        show -(τ - b * ε) + -(b * ε) = -τ by ring, one_mul] at hh
      simpa only [mul_comm] using hh
    exact hbase.trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hlow hε.le) (by positivity))
  refine ⟨hp, hhigh.trans hk.scale, hp1,
    hk.large.trans_le (Real.rpow_le_rpow_of_nonpos hp hhigh (by linarith)),
    hk.planes.trans hneg, hk.graphs.trans hneg, hk.support.trans hneg,
    scalar_local_fit_density_budget hp (hK k) hd hsmall, ?_⟩
  calc
    _ ≤ p ^ ε / (11426400 * K k ^ 14) := hlen
    _ = (p / (11426400 * K k ^ 14)) * p ^ (ε - 1) := by
      have he : p * p ^ (ε - 1) = p ^ ε := by
        calc
          _ = p ^ (1 : ℝ) * p ^ (ε - 1) := by rw [Real.rpow_one]
          _ = p ^ (1 + (ε - 1)) := (Real.rpow_add hp _ _).symm
          _ = _ := by congr 1; ring
      rw [div_mul_eq_mul_div, he]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (scalar_normalized_active_length_lower hp hp1 (hK k) hd) (Real.rpow_nonneg hp.le _)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
