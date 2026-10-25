/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAffineCoherence.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAffineCoherence.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative comparison of the affine fits on common original times. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Metric

theorem exists_separated_original_times {U : Set ℝ} {ell : ℝ} (hell : 0 < ell)
    (hU : ENNReal.ofReal ell ≤ volume U) :
    ∃ x ∈ U, ∃ y ∈ U, ell / 2 < |x - y| := by
  by_contra hn
  push Not at hn
  have hdiam : ediam U ≤ ENNReal.ofReal (ell / 2) :=
    ediam_le_of_forall_dist_le (fun x hx y hy => by simpa only [Real.dist_eq] using hn x hx y hy)
  have hle : ENNReal.ofReal ell ≤ ENNReal.ofReal (ell / 2) :=
    hU.trans ((Real.volume_le_diam U).trans hdiam)
  have hleR : ell ≤ ell / 2 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hle
  linarith

/-- Parent and child affine fits are compared on their common original
fitting times, even if later deletion removes some of those times. -/
theorem affine_slopes_close_on_long_set {U : Set ℝ} {f : ℝ → ℝ}
    {ell a b v w ε ε' : ℝ} (hell : 0 < ell)
    (hU : ENNReal.ofReal ell ≤ volume U)
    (hfit : ∀ t ∈ U, |f t - (a + v * t)| ≤ ε)
    (hfit' : ∀ t ∈ U, |f t - (b + w * t)| ≤ ε') :
    |v - w| ≤ 4 * (ε + ε') / ell := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_separated_original_times hell hU
  have hd t (ht : t ∈ U) : |(a + v * t) - (b + w * t)| ≤ ε + ε' := by
    calc
      _ ≤ |(a + v * t) - f t| + |f t - (b + w * t)| := abs_sub_le _ _ _
      _ ≤ ε + ε' := add_le_add (by simpa only [abs_sub_comm] using hfit t ht) (hfit' t ht)
  have hprod : |v - w| * |x - y| ≤ 2 * (ε + ε') := by
    calc
      _ = |((a + v * x) - (b + w * x)) - ((a + v * y) - (b + w * y))| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |(a + v * x) - (b + w * x)| + |(a + v * y) - (b + w * y)| := abs_sub _ _
      _ ≤ 2 * (ε + ε') := by linarith [hd x hx, hd y hy]
  apply (le_div_iff₀ hell).mpr
  have hsmall := mul_le_mul_of_nonneg_left hxy.le (abs_nonneg (v - w))
  nlinarith

theorem taylor_error_of_affine_fit {f : ℝ → ℝ} {u t a v A ε δ : ℝ}
    (hu : |f u - (a + v * u)| ≤ ε) (ht : |f t - (a + v * t)| ≤ ε)
    (hv : |v - A| ≤ δ) :
    |f t - f u - (t - u) * A| ≤ 2 * ε + |t - u| * δ := by
  have heq : f t - f u - (t - u) * A =
      (f t - (a + v * t)) - (f u - (a + v * u)) + (t - u) * (v - A) := by ring
  rw [heq]
  calc
    _ ≤ |f t - (a + v * t)| + |f u - (a + v * u)| + |(t - u) * (v - A)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 * ε + |t - u| * δ := by
      rw [abs_mul]
      have hmul := mul_le_mul_of_nonneg_left hv (abs_nonneg (t - u))
      linarith

open scoped BigOperators

/-- Every link uses its stored common fitting set, so subsequent deletions
do not change the chain's slope comparison. -/
theorem affine_hierarchy_slope {f : ℝ → ℝ} (n : ℕ)
    (a v ε ell : ℕ → ℝ) (U : ℕ → Set ℝ)
    (hell : ∀ i < n, 0 < ell i)
    (hU : ∀ i < n, ENNReal.ofReal (ell i) ≤ volume (U i))
    (hfit : ∀ i < n, ∀ t ∈ U i, |f t - (a i + v i * t)| ≤ ε i)
    (hfit' : ∀ i < n, ∀ t ∈ U i, |f t - (a (i + 1) + v (i + 1) * t)| ≤ ε (i + 1)) :
    |v 0 - v n| ≤ ∑ i ∈ Finset.range n, 4 * (ε i + ε (i + 1)) / ell i := by
  have h := dist_le_range_sum_of_dist_le (f := v) n (d := fun i => 4 * (ε i + ε (i + 1)) / ell i)
    (fun {i} hi => by simpa only [Real.dist_eq] using
      affine_slopes_close_on_long_set (hell i hi) (hU i hi) (hfit i hi) (hfit' i hi))
  simpa only [Real.dist_eq] using h

theorem affine_hierarchy_taylor {f : ℝ → ℝ} (n : ℕ)
    (a v ε ell : ℕ → ℝ) (U : ℕ → Set ℝ)
    (hell : ∀ i < n, 0 < ell i)
    (hU : ∀ i < n, ENNReal.ofReal (ell i) ≤ volume (U i))
    (hfit : ∀ i < n, ∀ t ∈ U i, |f t - (a i + v i * t)| ≤ ε i)
    (hfit' : ∀ i < n, ∀ t ∈ U i, |f t - (a (i + 1) + v (i + 1) * t)| ≤ ε (i + 1))
    {t u : ℝ} (ht : |f t - (a 0 + v 0 * t)| ≤ ε 0)
    (hu : |f u - (a 0 + v 0 * u)| ≤ ε 0) :
    |f t - f u - (t - u) * v n| ≤ 2 * ε 0 +
      |t - u| * (∑ i ∈ Finset.range n, 4 * (ε i + ε (i + 1)) / ell i) :=
  taylor_error_of_affine_fit hu ht (affine_hierarchy_slope n a v ε ell U hell hU hfit hfit')

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
