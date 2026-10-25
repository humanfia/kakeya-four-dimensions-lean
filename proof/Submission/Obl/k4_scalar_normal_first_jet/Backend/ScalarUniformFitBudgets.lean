/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformFitBudgets.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformFitBudgets.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalFitPowers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSlopeAsymptotics

/-! One eventual threshold for all the normalized local affine-fit inputs. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Filter
open scoped Topology
open Submission.Obl.k4_discrete_of_terminal_charts

structure ScalarLocalFitBudget (p K d σ ε η p₀ length : ℝ) : Prop where
  positive : 0 < p
  scale : p ≤ p₀
  unit : p ≤ 1
  large : 33 * (51 * K) < p ^ (ε - 1)
  planes : 11 ≤ p ^ (-η)
  graphs : 4 * (K + 1) + 3 ≤ p ^ (-η)
  support : (2 * (scalarLocalFitErrorCount K : ℝ) + 3) * K *
    (1 + 2 * (scalarLocalFitErrorCount K : ℝ)) ^ (1 - σ) ≤ p ^ (-η)
  collisions : 4 * ((51 * K) ^ 3 * p ^ (η - 3)) *
    (scalarCollisionPairCeiling p K d K (1 + 2 * K) * p) ≤ scalarNormalizedCollisionMass p K d K⁻¹
  time : length ≤ scalarNormalizedActiveLength p K d K K⁻¹ * p ^ (ε - 1)

theorem scalar_local_fit_budgets_eventually (N K : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {c d σ ε η p₀ τ : ℝ} (hc : 0 < c) (hd : d ≤ 1) (hσ : 0 < σ)
    (hε : ε < 1) (hη : 0 < η) (hp₀ : 0 < p₀) (hτ : c * ε < τ) :
    ∀ᶠ k in atTop, ScalarLocalFitBudget (N k ^ (-c)) (K k) d σ ε η p₀ (N k ^ (-τ)) := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hscale : ∀ᶠ k in atTop, N k ^ (-c) < p₀ :=
    ((tendsto_rpow_neg_atTop hc).comp hNt).eventually (gt_mem_nhds hp₀)
  have hdecay := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 5
    (a := c * η) (b := 1) (C := 899) (mul_pos hc hη) (by norm_num) (by norm_num)
  have hdensity := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 15
    (a := c * η) (b := 1) (C := 11000000000) (mul_pos hc hη) (by norm_num) (by norm_num)
  have hlarge := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 1
    (a := c * (1 - ε)) (b := 1) (C := 1683) (mul_pos hc (sub_pos.mpr hε)) (by norm_num) (by norm_num)
  have hlength := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 14
    (a := τ - c * ε) (b := 1) (C := 11426400) (sub_pos.mpr hτ) (by norm_num) (by norm_num)
  filter_upwards [hscale, hdecay, hdensity, hlarge, hlength] with k hscale hdecay hdensity hlarge hlength
  let p := N k ^ (-c)
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  have hp1 : p ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le (hN k) (show -c ≤ 0 by linarith)
  have hpη : p ^ η = N k ^ (-(c * η)) := by
    dsimp [p]
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hbound : 899 * K k ^ 5 ≤ p ^ (-η) := by
    rw [Real.rpow_neg hp.le, inv_eq_one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hp η)).mpr
    simpa only [hpη] using hdecay.le
  have hK5 : 1 ≤ K k ^ 5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (hK k) 5
  have hK15 : K k ≤ K k ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ (hK k) (by norm_num : 1 ≤ (5 : ℕ))
  have hplane : 11 ≤ 899 * K k ^ 5 := by linarith
  have hgraph : 4 * (K k + 1) + 3 ≤ 899 * K k ^ 5 := by linarith [hK k]
  have hlarge' : 33 * (51 * K k) < p ^ (ε - 1) := by
    have he : ε - 1 = -(1 - ε) := by ring
    have hpRate : p ^ (1 - ε) = N k ^ (-(c * (1 - ε))) := by
      dsimp [p]
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    rw [he, Real.rpow_neg hp.le, inv_eq_one_div]
    apply (lt_div_iff₀ (Real.rpow_pos_of_pos hp (1 - ε))).mpr
    rw [hpRate]
    convert hlarge using 1 <;> ring
  have hlen : N k ^ (-τ) ≤ p ^ ε / (11426400 * K k ^ 14) := by
    have hpε : p ^ ε = N k ^ (-(c * ε)) := by
      dsimp [p]
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring
    apply (le_div_iff₀ (by positivity : 0 < 11426400 * K k ^ 14)).mpr
    rw [hpε]
    have h := mul_le_mul_of_nonneg_right hlength.le (Real.rpow_nonneg hNpos.le (-(c * ε)))
    rw [mul_assoc, ← Real.rpow_add hNpos, show -(τ - c * ε) + -(c * ε) = -τ by ring, one_mul] at h
    simpa only [mul_comm] using h
  have hdensity' : 11000000000 * K k ^ 15 * p ^ η ≤ 1 := by
    rw [hpη]
    exact hdensity.le
  refine ⟨hp, hscale.le, hp1, hlarge', hplane.trans hbound, hgraph.trans hbound,
    (scalar_local_fit_support_budget (hK k) (by linarith : 1 - σ ≤ 1)).trans hbound,
    scalar_local_fit_density_budget hp (hK k) hd hdensity', ?_⟩
  calc
    _ ≤ p ^ ε / (11426400 * K k ^ 14) := hlen
    _ = (p / (11426400 * K k ^ 14)) * p ^ (ε - 1) := by
      have he : p * p ^ (ε - 1) = p ^ ε := by
        calc
          _ = p ^ (1 : ℝ) * p ^ (ε - 1) := by rw [Real.rpow_one]
          _ = p ^ (1 + (ε - 1)) := (Real.rpow_add hp _ _).symm
          _ = _ := by congr 1; ring
      rw [div_mul_eq_mul_div, he]
    _ ≤ _ := mul_le_mul_of_nonneg_right (scalar_normalized_active_length_lower hp hp1 (hK k) hd)
      (Real.rpow_nonneg hp.le _)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
