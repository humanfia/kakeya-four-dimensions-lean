import Submission.Obl.k4_quadratic_discriminant_safe_paths.Geometry
import Submission.Obl.k4_quadratic_discriminant_safe_paths.LinePolynomial
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Perturbation

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

theorem tube_small_imp_path_small (F : ComplexSpace → ℂ) {L r : ℝ}
    (hL : 0 ≤ L) (hr : r ≤ 1 / 2)
    (hLip : ∀ z w : ComplexSpace, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖F z - F w‖ ≤ L * dist z w)
    {a x : RealSpace} {τ : ℂ}
    (ha : ‖a‖ ≤ (1 : ℝ) / 8) (hx : ‖x‖ ≤ (1 : ℝ) / 8)
    (hτ : ‖τ‖ ≤ 1) {z : ComplexSpace}
    (hz : z ∈ thickening r (brokenPath a x τ)) (hsmall : ‖F z‖ < r) :
    ∃ w ∈ brokenPath a x τ, ‖F w‖ < (1 + L) * r := by
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
  have hwn : ‖w‖ ≤ (1 : ℝ) / 2 := brokenPath_norm_le ha hx hτ hw
  have hzn : ‖z‖ ≤ 1 := by
    have h := norm_add_le (z - w) w
    rw [sub_add_cancel, ← dist_eq_norm] at h
    linarith
  refine ⟨w, hw, ?_⟩
  have hlip := hLip z w hzn (by linarith)
  have htri : ‖F w‖ ≤ ‖F z - F w‖ + ‖F z‖ := by
    have h := norm_add_le (F w - F z) (F z)
    simpa only [sub_add_cancel, norm_sub_rev] using h
  nlinarith [mul_le_mul_of_nonneg_left hzw.le hL]

theorem volume_good_anchor_fiber (a x : RealSpace)
    (P P' : MvPolynomial (Fin 3) ℝ) {A L r δ κ : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : r ≤ 1 / 2)
    (hdeg : P.totalDegree ≤ 2) (hdeg' : P'.totalDegree ≤ 2)
    (hcoeff : ∀ d, |P.coeff d| ≤ A) (hcoeff' : ∀ d, |P'.coeff d| ≤ A)
    (hLip : ∀ (R : MvPolynomial (Fin 3) ℝ), R.totalDegree ≤ 2 →
      (∀ d, |R.coeff d| ≤ A) →
      ∀ z w : ComplexSpace, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
        ‖MvPolynomial.eval (fun i => z i) (R.map (algebraMap ℝ ℂ)) -
          MvPolynomial.eval (fun i => w i) (R.map (algebraMap ℝ ℂ))‖ ≤
        L * A * dist z w)
    (ha : ‖a‖ ≤ (1 : ℝ) / 8) (hx : ‖x‖ ≤ (1 : ℝ) / 8)
    (hδ₀ : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsource : κ ≤ |MvPolynomial.eval (fun i => a i) P|)
    (hsource' : κ ≤ |MvPolynomial.eval (fun i => a i) P'|)
    (hanchor : κ ≤ |MvPolynomial.eval (fun i => x i) P|)
    (hanchor' : κ ≤ |MvPolynomial.eval (fun i => x i) P'|)
    (hscale : (1 + L * A) * r ≤ κ * δ ^ 2) :
    volume (Prod.mk x ⁻¹' badSet a P P' r) ≤ ENNReal.ofReal (64 * δ) := by
  let T (R : MvPolynomial (Fin 3) ℝ) : Set ℂ :=
    {τ | τ ∈ closedBall (1 / 2 : ℂ) (1 / 4) ∧
      ∃ s ∈ segment ℝ (0 : ℂ) τ ∪ segment ℝ τ 1,
        ‖(linePolynomial R a x).eval s‖ < κ * δ ^ 2}
  have hvol (R : MvPolynomial (Fin 3) ℝ) (hR : R.totalDegree ≤ 2)
      (hs : κ ≤ |MvPolynomial.eval (fun i => a i) R|)
      (hxR : κ ≤ |MvPolynomial.eval (fun i => x i) R|) :
      volume (T R) ≤ ENNReal.ofReal (32 * δ) := by
    apply volume_broken_small_values (linePolynomial R a x)
      (linePolynomial_degree R a x hR) hδ₀ hδ
    · simpa only [linePolynomial_zero] using hs
    · simpa only [linePolynomial_one] using hxR
  have hsub : Prod.mk x ⁻¹' badSet a P P' r ⊆ T P ∪ T P' := by
    intro τ hτ
    rcases hτ with ⟨_, hτ, z, hz, hsmall⟩
    have hin (R : MvPolynomial (Fin 3) ℝ) (hR : R.totalDegree ≤ 2)
        (hcR : ∀ d, |R.coeff d| ≤ A)
        (hsmallR : ‖MvPolynomial.eval (fun i => z i)
          (R.map (algebraMap ℝ ℂ))‖ < r) : τ ∈ T R := by
      obtain ⟨w, hw, hval⟩ := tube_small_imp_path_small
        (fun z => MvPolynomial.eval (fun i => z i) (R.map (algebraMap ℝ ℂ)))
        (mul_nonneg hL hA) hr (hLip R hR hcR) ha hx (detour_norms hτ).1 hz hsmallR
      rw [brokenPath_image] at hw
      obtain ⟨s, hs, rfl⟩ := hw
      refine ⟨hτ, s, hs, ?_⟩
      rw [linePolynomial_eval]
      rw [complexLineAffine_apply] at hval
      exact hval.trans_le hscale
    exact hsmall.elim (fun h => Or.inl (hin P hdeg hcoeff h))
      (fun h => Or.inr (hin P' hdeg' hcoeff' h))
  calc
    _ ≤ volume (T P) + volume (T P') :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (32 * δ) + ENNReal.ofReal (32 * δ) :=
      add_le_add (hvol P hdeg hsource hanchor) (hvol P' hdeg' hsource' hanchor')
    _ = ENNReal.ofReal (64 * δ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Submission.Obl.k4_quadratic_discriminant_safe_paths
