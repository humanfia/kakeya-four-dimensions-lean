import Submission.Obl.k4_oss_dyadic_reduction.Mesh
import Submission.Obl.k4_oss_dyadic_reduction.Rescale
import Submission.Obl.k4_oss_dyadic_reduction.Scale

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_dyadic_reduction

noncomputable section

/-- The analytic reduction, with its small-scale numerical choices left explicit. -/
lemma norm_pi_mesh_le {n N : ℕ} {s ε τ δ₀ r ε₀ η D ξ : ℝ}
    (hcore : UnitDecay n s ε τ δ₀) (hs : 0 ≤ s) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hr : 0 < r) (hN : 0 < N) (hrN : r ≤ 1 / (N : ℝ))
    (hη : 0 < η) (hD : 0 < D) (hD₀ : D < δ₀)
    (hND : r * (N : ℝ) ^ n ≤ D)
    (hcoef : η⁻¹ * r ^ (-ε₀) ≤ D ^ (-ε))
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (hcap : FrostmanCap μ r s ε₀)
    (hξ1 : r⁻¹ ≤ |ξ|) (hξ2 : |ξ| ≤ 2 * r⁻¹) :
    ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => μ)‖ ≤
      D ^ τ + n * (r ^ (-ε₀) * (1 / (N : ℝ)) ^ s + 2 * N * η) := by
  classical
  have hgood : ‖∫ x, phase ξ x
      ∂Measure.pi (fun _ : Fin n => μ.restrict (goodRegion μ N η))‖ ≤ D ^ τ := by
    rw [restrict_goodRegion μ hN η]
    apply norm_integral_pi_sum_le _ (sum_goodCell_mass_le μ hN η)
      (Real.rpow_nonneg hD.le _) ξ
    intro p
    let a : Fin n → ℝ := fun j => signedScale (p j).val
    let S : Fin n → Set ℝ := fun j => meshCell (p j).val
    have ha0 (j : Fin n) : 0 < |a j| := by
      dsimp [a]
      rw [abs_signedScale hN]
      exact meshScale_pos hN _
    have ha (j : Fin n) : a j ≠ 0 := abs_pos.mp (ha0 j)
    have ha1 (j : Fin n) : |a j| ≤ 1 := by
      dsimp [a]
      rw [abs_signedScale hN]
      exact meshScale_le_one hN _
    have haN (j : Fin n) : 1 / (N : ℝ) ≤ |a j| := by
      dsimp [a]
      rw [abs_signedScale hN]
      exact meshScale_lower hN _
    let δ : ℝ := r / ∏ j, |a j|
    obtain ⟨hδ, hδN, hscale, hfreq⟩ := scale_data hN a ha0 ha1 haN hr
    have hδD : δ ≤ D := hδN.trans hND
    have hcoδ : η⁻¹ * r ^ (-ε₀) ≤ δ ^ (-ε) :=
      hcoef.trans (Real.rpow_le_rpow_of_nonpos hδ hδD (neg_nonpos.mpr hε))
    have hbox := norm_heavy_box_le μ S a hcore hr hs hδ (hδD.trans_lt hD₀) hη
      ha ha1 (fun j => meshCell_rescale hN (p j).val)
      (fun j => (p j).property) hscale hcoδ hcap
      (hfreq ξ hξ1 hξ2).1 (hfreq ξ hξ1 hξ2).2
      (Real.rpow_le_rpow hδ.le hδD hτ)
    simpa only [measureReal_restrict_apply MeasurableSet.univ, univ_inter] using hbox
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb1 : 1 / (N : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hNR
  have hdeep : μ.real (Icc (-(1 / N : ℝ)) (1 / N)) ≤
      r ^ (-ε₀) * (1 / (N : ℝ)) ^ s := by
    have hc := hcap 0 (1 / N) hrN hb1
    simpa only [zero_sub, zero_add, measureReal_def] using
      ENNReal.toReal_le_of_le_ofReal (by positivity) hc
  calc
    ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => μ)‖ ≤
        ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => μ.restrict (goodRegion μ N η))‖ +
          n * μ.real (goodRegion μ N η)ᶜ :=
      norm_integral_pi_cut_le μ _ (measurableSet_goodRegion μ N η) ξ
    _ ≤ D ^ τ + n *
        (μ.real (Icc (-(1 / N : ℝ)) (1 / N)) + 2 * N * η) := by
      gcongr
      exact discarded_mass_le μ hsupport hN hη.le
    _ ≤ _ := by gcongr

end
end Submission.Obl.k4_oss_dyadic_reduction
