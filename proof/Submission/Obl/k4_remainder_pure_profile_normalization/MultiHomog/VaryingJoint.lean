import Submission.Obl.k4_remainder_pure_profile_normalization.VaryingDepth
import Submission.Obl.k4_remainder_pure_profile_normalization.Profile
import Submission.Obl.k4_native_grid_profile_extension.ProfileBridge
import Submission.Obl.k4_joint_homogenization.Interface

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Filter Set
open scoped Topology ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

private noncomputable abbrev J := Submission.Obl.k4_joint_homogenization.Observation
private noncomputable abbrev Ref := Submission.Obl.k4_joint_homogenization.Reference

/-- The single-world profile at angular depth zero also controls any converging
sequence of hidden depths, for every measurable density representative. -/
theorem typical_joint_at_tendsto_depth
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (ht : Tendsto N atTop atTop)
    (μ : ℕ → Measure Incidence) [∀ k, IsFiniteMeasure (μ k)]
    {R : ℝ} (hR : 0 ≤ R) (F : ℝ → ℝ → ℝ)
    (hF : Submission.Obl.k4_joint_homogenization.ProfileRegular R 1 F)
    (hd : Submission.Obl.k4_joint_homogenization.DensityExists N μ R 1)
    (htyp : Submission.Obl.k4_joint_homogenization.Typical N μ R 1 F)
    (a : ℕ → ℝ) (ha : ∀ k, a k ∈ Icc (0 : ℝ) R) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) R) (hat : Tendsto a atTop (𝓝 r))
    (g : ℕ → JointObservation → ENNReal) (hg : ∀ k, Measurable (g k))
    (hmap : ∀ k, (μ k).map (J (N k) (a k) 0) = Ref.withDensity (g k)) :
    HasTypicalDensity N μ (fun k z => g k (J (N k) (a k) 0 z)) (F r 0) := by
  let d := fun k s =>
    Submission.Obl.k4_native_grid_profile_extension.nativeDensity (μ k) (N k) s 0
  have hdm (k : ℕ) (s : ℝ) : Measurable (d k s) :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_nativeDensity _ _ _ _
  have hdl (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) :
      (μ k).map (J (N k) s 0) = Ref.withDensity (d k s) := by
    have H := Submission.Obl.k4_native_grid_profile_extension.nativeDensity_law
      (μ k) (N k) s 0 (hd k s 0 hs.1 hs.2 le_rfl (by norm_num))
    simpa only [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation,
      Submission.Obl.k4_native_grid_profile_extension.nativeReference, J, Ref, d]
      using H
  have hfixed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) :
      HasTypicalDensity N μ (fun k z => d k s (J (N k) s 0 z)) (F s 0) := by
    intro τ hτ
    obtain ⟨c,hc,hb⟩ := htyp s 0 τ hs.1 hs.2 le_rfl (by norm_num) hτ
    exact ⟨c,hc,hb.mono fun k hk => hk (d k s) (hdm k s) (hdl k s hs)⟩
  have hmono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) (t : ℝ)
      (ht' : t ∈ Icc (0 : ℝ) R) (hst : s ≤ t) (k : ℕ) :
      ∀ᵐ z ∂μ k, d k t (J (N k) t 0 z) ≤ d k s (J (N k) s 0 z) := by
    have H := Submission.Obl.k4_native_grid_profile_extension.native_refinement_density_le
      (μ k) (hN k) hs.1 hst (u := 0) (v := 0) le_rfl le_rfl
      (d k s) (d k t) (hdm k s) (hdm k t)
    simpa only [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation,
      Submission.Obl.k4_native_grid_profile_extension.nativeReference, J, Ref, d]
      using H
        (by simpa only [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation,
          Submission.Obl.k4_native_grid_profile_extension.nativeReference, J, Ref] using hdl k s hs)
        (by simpa only [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation,
          Submission.Obl.k4_native_grid_profile_extension.nativeReference, J, Ref] using hdl k t ht')
  have hf : ProfileIncrement (fun s => F s 0) R :=
    fun s t hs hst ht' => hF.1 s t 0 hs hst ht' le_rfl (by norm_num)
  have H := typicalDensity_on_Icc_at_tendsto_depth N hN ht μ
    (fun s k z => d k s (J (N k) s 0 z)) (fun s => F s 0)
    hR hf.continuousOn hfixed hmono hr hat (Eventually.of_forall ha)
  intro τ hτ
  obtain ⟨c,hc,hb⟩ := H τ hτ
  refine ⟨c,hc,hb.mono fun k hk => ?_⟩
  have heq := Submission.Obl.k4_native_grid_profile_extension.observation_density_bad_mass_eq
    (μ k) Ref (J (N k) (a k) 0)
    (by
      simpa only [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation]
        using (Submission.Obl.k4_native_grid_profile_extension.measurable_nativeObservation
          (N k) (a k) 0))
    (g k) (d k (a k)) (hg k) (hdm k (a k)) (hmap k) (hdl k (a k) (ha k))
    (ENNReal.ofReal (N k ^ (-F r 0 - τ))) (ENNReal.ofReal (N k ^ (-F r 0 + τ)))
  exact heq.trans_le hk

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
