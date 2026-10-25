/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarFitNumerics.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarFitTransfer
import Submission.Obl.k4_scalar_graph_residual_discovery.FitNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- The eighth-power gain supplied by the scalar-normal theorem absorbs
every fixed subpower factor in the original row transfer. -/
theorem eventually_eighth_gain {N H K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ : ℝ}
    (hκ : 0 < κ) (hh : ∀ k, 0 < h k)
    (hscale : ∀ᶠ k in atTop, h k ≤ K k * N k ^ (-κ)) :
    ∀ᶠ k in atTop, H k * h k ^ ((1 : ℝ) / 8) ≤ 1 / 2 := by
  have hH' : Subpower N (fun k => 4 * H k ^ 2) :=
    subpower_polynomial hN hNt hH (by norm_num) 2
  filter_upwards [eventually_discovery_slack hN hNt hH' hK hκ (by norm_num : (0 : ℝ) < 1)
    hh hscale] with k hk
  have hsquare : (h k ^ ((1 : ℝ) / 8)) ^ 2 = h k ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hh k).le]
    norm_num
  have hquarter := hk.2.1
  change 4 * H k ^ 2 * h k ^ ((1 : ℝ) / 4) ≤ 1 / 2 at hquarter
  have hnonneg : 0 ≤ H k * h k ^ ((1 : ℝ) / 8) :=
    mul_nonneg (by linarith [hH.1 k]) (Real.rpow_nonneg (hh k).le _)
  have hsq : 4 * (H k * h k ^ ((1 : ℝ) / 8)) ^ 2 ≤ 1 / 2 := by
    rw [mul_pow, hsquare]
    nlinarith only [hquarter]
  nlinarith

theorem eventually_scalar_row_coefficient_slack {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, 3 * H k + (1 + H k) * N k ^ (ε / 4) ≤ N k ^ (ε / 2) := by
  have hsmall := eventually_subpower_mul_rpow_lt hN hNt hH.1 hH.2 1
    (a := ε / 4) (b := ε / 2) (by linarith) (A := 8) (by norm_num)
  filter_upwards [hsmall] with k hk
  have hH1 := hH.1 k
  have hB : 1 ≤ N k ^ (ε / 4) := Real.one_le_rpow (hN k) (by positivity)
  simp only [pow_one] at hk
  nlinarith

/-- All final row allowances follow from the scalar fit without shortening
its original labeled fiber. Only the ORIGINAL coefficient factor is subpower;
no such assertion is made about the finite-grid geometric world budget. -/
theorem eventually_scalar_fit_to_discovery_slack {N H K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hh : ∀ k, 0 < h k)
    (hscale : ∀ᶠ k in atTop, h k ≤ K k * N k ^ (-κ))
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ k in atTop, ∀ (E : Set ScalarIncidence) (G : ScalarIncidence → Fin 2 → ℝ)
      (F : ℝ → ℝ) (P : Polynomial ℝ) (p : ScalarIncidence) (I : Set ℝ),
      p ∈ E → (∀ e, |p.1.2 e| ≤ H k) → P.natDegree ≤ M →
      (∀ a : ℕ, |P.coeff a| ≤ N k ^ (ε / 4)) →
      (∀ z ∈ E, |z.1.2 3 + 2 * z.2 * z.1.2 4 - G z 0 - G z 1 * z.1.2 1| ≤
        h k ^ M * h k ^ ((1 : ℝ) / 8)) →
      (∀ z ∈ E, |G z 1 - F z.2| ≤ h k ^ M * h k ^ ((1 : ℝ) / 8)) →
      |F p.2 - P.eval p.2| ≤ h k ^ M * h k ^ ((1 : ℝ) / 8) →
      ENNReal.ofReal (h k * N k ^ (-(ε / 4))) ≤
        volume {t | (p.1, t) ∈ E ∧ t ∈ I ∧
          |F t - P.eval t| ≤ h k ^ M * h k ^ ((1 : ℝ) / 8)} →
      FitsWith E G I M (N k ^ (ε / 2)) (h k ^ M / 2)
        (h k * N k ^ (-(ε / 2))) p (recoverRowPolynomial p.1 P) := by
  have hH' : Subpower N (fun k => 5 * H k) := by
    simpa only [pow_one] using subpower_polynomial hN hNt hH (by norm_num : (1 : ℝ) ≤ 5) 1
  filter_upwards [eventually_eighth_gain hN hNt hH' hK hκ hh hscale,
    eventually_scalar_row_coefficient_slack hN hNt hH hε] with k hgain hcoef
  intro E G F P p I hp hcoeff hdeg hP hgraph hrow hpoint hduration
  have hH0 : 0 ≤ H k := by linarith [hH.1 k]
  have hB0 : 0 ≤ N k ^ (ε / 4) := Real.rpow_nonneg (by linarith [hN k]) _
  have hfit := row_fit_of_scalar_fit F P hp hM hH0 hB0 hcoeff hdeg hP
    hgraph hrow hpoint hduration
  apply hfit.mono (Subset.rfl) (Subset.rfl) le_rfl hcoef
  · have hpow : 0 ≤ h k ^ M := (pow_pos (hh k) M).le
    have hsmall : (3 + 2 * H k) * h k ^ ((1 : ℝ) / 8) ≤ 1 / 2 := by
      have hH1 := hH.1 k
      change 5 * H k * h k ^ ((1 : ℝ) / 8) ≤ 1 / 2 at hgain
      nlinarith [Real.rpow_nonneg (hh k).le ((1 : ℝ) / 8)]
    have hmul := mul_le_mul_of_nonneg_left hsmall hpow
    nlinarith only [hmul]
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith : -(ε / 2) ≤ -(ε / 4))) (hh k).le

end Submission.Obl.k4_scalar_graph_residual_discovery
