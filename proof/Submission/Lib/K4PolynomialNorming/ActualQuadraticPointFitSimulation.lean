/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualAffineLineSimulation
import Submission.Lib.K4PolynomialNorming.WholeBlockLineField

open Set MeasureTheory ProbabilityTheory MvPolynomial
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Original pointwise incidence fits, original long-line time ceilings,
and shared-state cell geometry produce the actual six-switch simulation.
Whole-block fitting is derived by Remez within the original incidence law. -/
theorem actual_quadratic_six_switch_endpoint_error_of_original_point_fit_ae {L Q C : Type*}
    [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace Q] [StandardBorelSpace Q] [MeasurableSpace C]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → C) (v : C → EuclideanSpace ℝ (Fin 3))
    (a h : ℝ) (hh : 0 < h) (Long : Set L) (hLong : MeasurableSet Long)
    (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
    (hb : Measurable base) (hu : Measurable velocity)
    (hz₀ : Measurable height₀) (hz₁ : Measurable height₁) (hz₂ : Measurable height₂)
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (D : ℕ) (hD : ∀ j, (T j).totalDegree ≤ D)
    (Ktime : ℝ) (hKtime : 1 ≤ Ktime)
    (htimeLong : ∀ l ∈ Long,
      κ l ≤ ((ENNReal.ofReal h)⁻¹*ENNReal.ofReal Ktime) • volume)
    (ε η τ ζ B U A R : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a+h))
    (hvelocity : ∀ᵐ z ∂ν ⊗ₘ κ,
      ‖velocity z.1-(fun j : Fin 3 => v (control z.1) j)‖ ≤ τ)
    (hcodes : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
    (hfit : ∀ᵐ z ∂ν ⊗ₘ κ,
      |quadraticHeightSpeed (height₁ z.1) (height₂ z.1) ((z.2-a)/h)-∑ j,
        velocity z.1 j * MvPolynomial.eval
          (base z.1+((z.2-a)/h) • velocity z.1) (T j)| ≤ ε)
    (hconf : ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1, ‖base z.1+t • velocity z.1‖ ≤ R)
    (hfield : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j, |MvPolynomial.eval x (T j)| ≤ B)
    (hspace : ∀ x ∈ Metric.closedBall 0 (R+7*(η+τ)),
      ∀ y ∈ Metric.closedBall 0 (R+7*(η+τ)), ∀ j,
        |MvPolynomial.eval x (T j)-MvPolynomial.eval y (T j)| ≤ A*‖x-y‖)
    (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂ν ⊗ₘ κ, Valid z)
    (hshared : ∀ old redraw, state redraw = state old → Valid old → Valid redraw →
      (old.2-a)/h ∈ Icc (0:ℝ) 1 → redraw.1 ∈ Long →
      ‖(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2-a)/h)).1-
        (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).1‖ ≤ η ∧
      |(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2-a)/h)).2-
        (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).2| ≤ ζ)
    (w : (ℕ → L × ℝ) → ENNReal)
    (hretainedLong : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      ∀ k < 6, (x (k+1)).1 ∈ Long) :
    ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      let q := codedSixSwitchEndpoint T
        (fun z => (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1) v
        (sixSwitchCoordinates control a h x)
      let p₀ := quadraticIncidencePoint a h base velocity height₀ height₁ height₂ (x 0)
      let p₆ := quadraticIncidencePoint a h base velocity height₀ height₁ height₂ (x 6)
      ‖q.1+p₀.1-p₆.1‖ ≤ 6*(η+τ) ∧
      |q.2+p₀.2-p₆.2| ≤ 6*(ζ+((8*((D:ℝ)+2)*Ktime)^(D+1)*ε)+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ))) ∧
      ‖q+p₀-p₆‖ ≤ max (6*(η+τ))
        (6*(ζ+((8*((D:ℝ)+2)*Ktime)^(D+1)*ε)+(3*B)*τ+(3*U*A)*(η+τ)+(3*U*A)*(6*(η+τ)))) := by
  have htimes : ∀ᵐ z ∂ν ⊗ₘ κ, (z.2-a)/h ∈ Icc (0:ℝ) 1 := by
    filter_upwards [ht] with z hz
    exact normalized_time_mem_unit_interval hh hz
  have hnorm : Measurable (fun t : ℝ => (t-a)/h) := by fun_prop
  have hnormcap : ∀ l ∈ Long,
      (κ l).map (fun t => (t-a)/h) ≤ ENNReal.ofReal Ktime • volume := by
    intro l hl
    have hm := Measure.map_mono (htimeLong l hl) hnorm
    rw [Measure.map_smul _ hnorm.aemeasurable,
      Submission.Lib.K4ChartLifting.map_volume_affine a h hh,smul_smul] at hm
    have hc : ((ENNReal.ofReal h)⁻¹*ENNReal.ofReal Ktime)*ENNReal.ofReal h =
        ENNReal.ofReal Ktime := by
      calc
        _ = ENNReal.ofReal Ktime*((ENNReal.ofReal h)⁻¹*ENNReal.ofReal h) := by ac_rfl
        _ = _ := by
          rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne'
            ENNReal.ofReal_ne_top,mul_one]
    simpa only [hc] using hm
  have hwhole := original_incidence_quadratic_field_fit_on_whole_block_ae ν κ
    (fun t => (t-a)/h) (by fun_prop) T D hD base velocity height₁ height₂
    Long Ktime ε hKtime hε hnormcap htimes
    (by simpa only [quadraticHeightSpeed] using hfit)
  have hKtime0 : 0 ≤ Ktime := by linarith
  have hεwhole : 0 ≤ (8*((D:ℝ)+2)*Ktime)^(D+1)*ε := by positivity
  exact actual_quadratic_six_switch_endpoint_error_ae ν κ state hstate control v a h hh
    Long hLong base velocity height₀ height₁ height₂ hb hu hz₀ hz₁ hz₂ T
    ((8*((D:ℝ)+2)*Ktime)^(D+1)*ε) η τ ζ B U A R hεwhole hη hτ hB hU hA
    ht hvelocity hcodes (by simpa only [quadraticHeightSpeed] using hwhole) hconf hfield hspace
    Valid hValid hshared w hretainedLong

end Submission.Lib.K4PolynomialNorming
