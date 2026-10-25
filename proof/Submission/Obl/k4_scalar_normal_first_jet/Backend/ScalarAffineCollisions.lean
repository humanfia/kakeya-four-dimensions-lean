/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAffineCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAffineCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineCoherence
import Mathlib.MeasureTheory.Measure.Prod

/-! Original time mass of collisions between separated affine slopes. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Metric
open scoped ENNReal

theorem affine_collision_time_cap {T : Set ℝ} {F F' : ℝ → ℝ}
    {a a' k k' p err Δ : ℝ} (hΔ : 0 < Δ) (hsep : Δ ≤ |k - k'|)
    (hF : ∀ t ∈ T, |F t - (a + k * t)| ≤ err)
    (hF' : ∀ t ∈ T, |F' t - (a' + k' * t)| ≤ err)
    (hcollision : ∀ t ∈ T, |F t - F' t| ≤ p) :
    volume T ≤ ENNReal.ofReal (2 * (p + 2 * err) / Δ) := by
  have hdiff t (ht : t ∈ T) : |(a + k * t) - (a' + k' * t)| ≤ p + 2 * err := by
    calc
      _ ≤ |(a + k * t) - F t| + |F t - F' t| + |F' t - (a' + k' * t)| := by
        exact (abs_sub_le _ (F t) _).trans
          (add_le_add le_rfl (abs_sub_le (F t) (F' t) _)) |>.trans_eq (by ring)
      _ ≤ p + 2 * err := by
        rw [abs_sub_comm (a + k * t) (F t)]
        linarith [hF t ht, hF' t ht, hcollision t ht]
  apply (Real.volume_le_diam T).trans
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  apply (le_div_iff₀ hΔ).mpr
  have hprod : |k - k'| * |x - y| ≤ 2 * (p + 2 * err) := by
    calc
      _ = |((a + k * x) - (a' + k' * x)) - ((a + k * y) - (a' + k' * y))| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |(a + k * x) - (a' + k' * x)| + |(a + k * y) - (a' + k' * y)| := abs_sub _ _
      _ ≤ _ := by linarith [hdiff x hx, hdiff y hy]
  rw [Real.dist_eq]
  have hsmaller := mul_le_mul_of_nonneg_right hsep (abs_nonneg (x - y))
  nlinarith

/-- The integrated far-slope ceiling uses the product of the two ORIGINAL
trajectory masses. The time law may be any measure dominated by volume. -/
theorem original_far_slope_collision_cap {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure ℝ) [SFinite μ] (hμ : μ ≤ volume)
    (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (ℝ × (Λ × Λ))} (hE : MeasurableSet E)
    (F : ℝ → Λ → ℝ) (a k : Λ → ℝ) {p err Δ : ℝ}
    (hp : 0 ≤ p) (herr : 0 ≤ err) (hΔ : 0 < Δ)
    (hconditions : ∀ q ∈ E, Δ ≤ |k q.2.1 - k q.2.2| ∧
      |F q.1 q.2.1 - (a q.2.1 + k q.2.1 * q.1)| ≤ err ∧
      |F q.1 q.2.2 - (a q.2.2 + k q.2.2 * q.1)| ≤ err ∧
      |F q.1 q.2.1 - F q.1 q.2.2| ≤ p) :
    (μ.prod (ν.prod ν)).real E ≤ (2 * (p + 2 * err) / Δ) * (ν.real univ) ^ 2 := by
  let r : ℝ := 2 * (p + 2 * err) / Δ
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpoint : ∀ q : Λ × Λ, μ ((fun t => (t, q)) ⁻¹' E) ≤ ENNReal.ofReal r := by
    intro q
    let T : Set ℝ := (fun t => (t, q)) ⁻¹' E
    apply (hμ T).trans
    by_cases hn : T.Nonempty
    · obtain ⟨t, ht⟩ := hn
      have hsep := (hconditions (t, q) ht).1
      exact affine_collision_time_cap (F := fun s => F s q.1) (F' := fun s => F s q.2)
        (a := a q.1) (a' := a q.2) (k := k q.1) (k' := k q.2) hΔ hsep
        (fun t ht => (hconditions (t, q) ht).2.1)
        (fun t ht => (hconditions (t, q) ht).2.2.1)
        (fun t ht => (hconditions (t, q) ht).2.2.2)
    · simp only [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty, zero_le]
  have hbound : (μ.prod (ν.prod ν)) E ≤ ENNReal.ofReal r * (ν univ) ^ 2 := by
    rw [Measure.prod_apply_symm hE]
    calc
      _ ≤ ∫⁻ _q : Λ × Λ, ENNReal.ofReal r ∂ν.prod ν := lintegral_mono hpoint
      _ = _ := by rw [lintegral_const, ← univ_prod_univ, Measure.prod_prod, pow_two]
  have hf : ENNReal.ofReal r * (ν univ) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (measure_ne_top ν _))
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, r] using
    ENNReal.toReal_mono hf hbound

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
