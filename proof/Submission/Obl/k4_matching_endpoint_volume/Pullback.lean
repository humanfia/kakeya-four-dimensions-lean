import Submission.Obl.k4_bounded_fiber_volume
import Submission.Obl.k4_matching_endpoint_volume.LocalInjectivity
import Submission.Obl.k4_matching_endpoint_volume.GridPacking

/-!
# Pullback volume from a quantitative injectivity radius

This combines the accepted general area inequality with a polynomial grid
bound for the separated points of a regular fiber.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set MeasureTheory
open scoped ENNReal NNReal

/-- A uniform lower derivative bound and a Lipschitz derivative give a
polynomial bound for pullback volume on a regular subset of the unit cube. -/
theorem unitCube_pullback_bound {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (hR : MeasurableSet R) (hRsub : R ⊆ Metric.closedBall 0 1)
    (hf : ContDiff ℝ 1 f) (L : ℝ≥0) {δ r d₀ : ℝ} (hr : 0 < r) (hd₀ : 0 < d₀)
    (hsmall : (L : ℝ) * r < δ)
    (hlip : LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall 0 1))
    (hlower : ∀ x ∈ R, ∀ v : Fin m → ℝ, δ * ‖v‖ ≤ ‖fderiv ℝ f x v‖)
    (hjac : ∀ x ∈ R, d₀ ≤ |(fderiv ℝ f x).det|)
    (A : Set (Fin m → ℝ)) (hA : MeasurableSet A) :
    volume (R ∩ f ⁻¹' A) ≤ ENNReal.ofReal (((4 / r + 2) ^ m + 1) / d₀) * volume A := by
  classical
  let S := R ∩ f ⁻¹' A
  let M : ℕ := ⌈(4 / r + 2) ^ m⌉₊
  have hS : MeasurableSet S := hR.inter (hA.preimage hf.continuous.measurable)
  have hdiff (x : Fin m → ℝ) : DifferentiableAt ℝ f x :=
    (hf.differentiable (by norm_num)) x
  have hfiber (y : Fin m → ℝ) : {x : Fin m → ℝ | x ∈ S ∧ f x = y}.Finite ∧
      {x : Fin m → ℝ | x ∈ S ∧ f x = y}.ncard ≤ M := by
    have hp := finite_ncard_le_of_cube_separated {x : Fin m → ℝ | x ∈ S ∧ f x = y}
      (by norm_num : (0 : ℝ) ≤ 1) hr ?_ ?_
    · refine ⟨hp.1, ?_⟩
      have hc : ({x : Fin m → ℝ | x ∈ S ∧ f x = y}.ncard : ℝ) ≤ (M : ℝ) := by
        apply hp.2.trans
        simpa only [mul_one, M] using (Nat.le_ceil ((4 / r + 2) ^ m))
      exact_mod_cast hc
    · intro x hx
      simpa only [Metric.mem_closedBall, dist_zero_right] using hRsub hx.1.1
    · intro x hx z hz hne
      exact fiber_separation_of_lipschitz_fderiv (convex_closedBall (0 : Fin m → ℝ) 1)
        hRsub L hr.le hsmall (fun x hx => hdiff x) hlip hlower hx.1.1 hz.1.1 hne
        (hx.2.trans hz.2.symm)
  have hlocal (x : Fin m → ℝ) (hx : x ∈ S) :
      ∃ V : Set (Fin m → ℝ), IsOpen V ∧ x ∈ V ∧ InjOn f V := by
    apply Submission.Obl.k4_bounded_fiber_volume.exists_open_injOn_of_contDiffAt_det_ne_zero
      f x hf.contDiffAt
    exact abs_pos.mp (hd₀.trans_le (hjac x hx.1))
  have hupper :=
    Submission.Obl.k4_bounded_fiber_volume.lintegral_abs_det_le_of_local_inj_finite_fibers
      volume S hS f (fderiv ℝ f) (fun x hx => (hdiff x).hasFDerivAt.hasFDerivWithinAt)
      hlocal A hA (fun x hx => hx.2) M (fun y hy => hfiber y)
  have hlowerVol : ENNReal.ofReal d₀ * volume S ≤
      ∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ f x).det| := by
    rw [← setLIntegral_const S]
    apply setLIntegral_mono' hS
    intro x hx
    exact ENNReal.ofReal_le_ofReal (hjac x hx.1)
  have hpre : volume S ≤ ENNReal.ofReal ((M : ℝ) / d₀) * volume A := by
    have hne : ENNReal.ofReal d₀ ≠ 0 := by positivity
    have htop : ENNReal.ofReal d₀ ≠ ⊤ := ENNReal.ofReal_ne_top
    apply (ENNReal.mul_le_mul_iff_right hne htop).mp
    have heq : ENNReal.ofReal d₀ * (ENNReal.ofReal ((M : ℝ) / d₀) * volume A) =
        (M : ENNReal) * volume A := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hd₀.le]
      rw [show d₀ * ((M : ℝ) / d₀) = (M : ℝ) by field_simp, ENNReal.ofReal_natCast]
    rw [heq]
    exact hlowerVol.trans hupper
  apply hpre.trans
  gcongr
  have hnonneg : 0 ≤ (4 / r + 2) ^ m := by positivity
  exact (Nat.ceil_lt_add_one hnonneg).le

end Submission.Obl.k4_matching_endpoint_volume
