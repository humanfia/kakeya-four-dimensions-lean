import Submission.Obl.k4_remainder_angular_cap_transport.Coarsening
import Submission.Obl.k4_remainder_angular_cap_transport.DensityTail
import Submission.Obl.k4_remainder_angular_cap_transport.Numerics

namespace Submission.Obl.k4_remainder_angular_cap_transport
open MeasureTheory Set
open Geometry
open scoped ENNReal

namespace Geometry.Frame
variable (H : Geometry.Frame)

/-- Transfer one original angular ceiling through a chart and any further incidence selection. -/
theorem selected_joint_tail (hq : 0 < H.q) (hD : IsUnit H.D.det)
    (ν : Measure Trajectory) [IsFiniteMeasure ν]
    (A : Set Trajectory) (F E E₂ : Set Incidence)
    (hA : MeasurableSet A) (hF : MeasurableSet F) (hFE : F ⊆ E)
    (hsub : ∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ Icc H.t₀ (H.t₀ + H.q))
    (hE₂ : E₂ ⊆ H.normEvent A F) (hpos : 0 < (ν A).toReal)
    (B δ a a₀ du κ : ℝ) (hδ : δ ≠ 0) (hdu : 0 < du) (hκ : 1 ≤ κ)
    (hDs : (∑ i : Fin 2, ∑ j : Fin 2, |H.D i j|) ≤ κ * H.q)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≤ 2) (hwidth : δ * a = a₀ * (m : ℝ))
    (G G₂ : ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hG : Measurable G) (hG₂ : Measurable G₂)
    (hlaw : ((ν.prod volume).restrict E).map (jobs B a₀ du) = jointRef.withDensity G)
    (hlaw₂ : ((((ν A)⁻¹ • (ν.restrict A).map H.normTraj).prod volume).restrict E₂).map
      (jobs (B / δ) a du) = jointRef.withDensity G₂)
    [hfinite : IsFiniteMeasure ((((ν A)⁻¹ • (ν.restrict A).map H.normTraj).prod volume).restrict E₂)]
    (θ : ENNReal) :
    (((ν A)⁻¹ • (ν.restrict A).map H.normTraj).prod volume).restrict E₂
      {p | ENNReal.ofReal (100 * κ ^ 2) * θ * ENNReal.ofReal (|H.D.det| / (ν A).toReal) <
        G₂ (jobs (B / δ) a du p)} ≤
      2 * (ν A * ENNReal.ofReal H.q)⁻¹ *
        ((ν.prod volume).restrict F) {p | θ < G (jobs B a₀ du p)} := by
  let μ := ((ν.prod volume).restrict F)
  let μ₂ := (((ν A)⁻¹ • (ν.restrict A).map H.normTraj).prod volume).restrict E₂
  let S : Set Incidence := {p | G (jobs B a₀ du p) ≤ θ}
  let α := (ν A * ENNReal.ofReal H.q)⁻¹
  let J := ENNReal.ofReal |H.obsMatrix.det|⁻¹
  let V := (((2 * ⌈κ⌉ + 1).toNat : ENNReal) ^ 2)
  have hS : MeasurableSet S := measurableSet_le (hG.comp (measurable_jobs _ _ _)) measurable_const
  have hμ₂ : μ₂ = (α • μ.map H.normInc).restrict E₂ := by
    rw [← H.normalized_selected_law hq hD ν hA hF hsub,
      Measure.restrict_restrict_of_subset hE₂]
  have hraw : (μ.restrict S).map (jobs B a₀ du) ≤ θ • jointRef := by
    calc
      _ ≤ (((ν.prod volume).restrict E).restrict S).map (jobs B a₀ du) :=
        Measure.map_mono (Measure.restrict_mono le_rfl (Measure.restrict_mono hFE le_rfl))
          (measurable_jobs _ _ _)
      _ ≤ _ := good_law_le _ _ _ (measurable_jobs _ _ _) G hG hlaw θ
  have hcoarse : (μ.restrict S).map (jobs B (δ * a) du) ≤ (θ * 2) • jointRef := by
    refine (coarsened_jobs_le (μ.restrict S) B a₀ (δ * a) du hm hwidth θ hraw).trans ?_
    have hm' : (m : ENNReal) ≤ 2 := by exact_mod_cast hm2
    gcongr
  have hnorm : ((μ.restrict S).map H.normInc).map (jobs (B / δ) a du) ≤
      ((θ * 2) * (J * V)) • jointRef :=
    H.normalized_joint_le hq hD hdu (by linarith) hDs (μ.restrict S) B δ a hδ (θ * 2) hcoarse
  have htail := pushforward_restriction_tail μ H.normInc H.measurable_normInc E₂ μ₂ α hμ₂
    jointRef (jobs (B / δ) a du) (measurable_jobs _ _ _) G₂ hG₂ hlaw₂ S hS _ hnorm
  have hthreshold : 2 * (α * ((θ * 2) * (J * V))) ≤
      ENNReal.ofReal (100 * κ ^ 2) * θ * ENNReal.ofReal (|H.D.det| / (ν A).toReal) := by
    have hj : α * J = ENNReal.ofReal (|H.D.det| / (ν A).toReal) :=
      H.conditioning_jacobian hq ν A hpos
    calc
      _ = 4 * θ * (α * J) * V := by ring
      _ ≤ 4 * θ * (α * J) * ENNReal.ofReal (25 * κ ^ 2) := by
        gcongr
        exact cover_multiplicity_le hκ
      _ = _ := by
        have h100 : ENNReal.ofReal (100 * κ ^ 2) = 4 * ENNReal.ofReal (25 * κ ^ 2) := by
          rw [show (100 * κ ^ 2 : ℝ) = 4 * (25 * κ ^ 2) by ring,
            ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [hj, h100]
        ring
  have hSc : Sᶜ = {p | θ < G (jobs B a₀ du p)} := by ext p; simp [S, not_le]
  calc
    _ ≤ μ₂ {p | 2 * (α * ((θ * 2) * (J * V))) < G₂ (jobs (B / δ) a du p)} :=
      measure_mono (fun _ hp => hthreshold.trans_lt hp)
    _ ≤ 2 * α * μ Sᶜ := htail
    _ = _ := by rw [hSc]

end Geometry.Frame
end Submission.Obl.k4_remainder_angular_cap_transport
