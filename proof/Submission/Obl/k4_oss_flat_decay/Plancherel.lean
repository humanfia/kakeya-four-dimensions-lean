import Mathlib

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory FourierTransform
open scoped FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- Inlined from LOT tree annals_bose_gases (another tree's accepted result):
--   Submission.Obl.BoseGases__restricted_kinetic_domain.fourier_ae_eq_L2, obligation o034, Submission/Obl/BoseGases__restricted_kinetic_domain/Plancherel.lean:11-40, lib 487c0679f25d.
--   where it stands there: namespace Submission.Obl.BoseGases__restricted_kinetic_domain | open MeasureTheory FourierTransform | open scoped FourierTransform | variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma fourier_ae_eq_L2 {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 volume) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1).locallyIntegrable
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  intro g hg hc
  let s : SchwartzMap V ℂ := (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have hs (x : V) : s x = (g x : ℂ) := rfl
  have hswap : (∫ x, s x * 𝓕 f x) = ∫ x, 𝓕 s x * f x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ V) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner s.integrable hf1
    simpa only [smul_eq_mul, flip_innerₗ, SchwartzMap.fourier_coe, Real.fourier_eq,
      VectorFourier.fourierIntegral, innerₗ_apply_apply] using h.symm
  have hdist := congrArg (fun T : TemperedDistribution V ℂ => T s)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at hdist
  calc
    (∫ x, g x • 𝓕 f x) = ∫ x, s x * 𝓕 f x := by
      simp only [hs, Complex.real_smul, smul_eq_mul]
    _ = ∫ x, 𝓕 s x * f x := hswap
    _ = ∫ x, 𝓕 s x • hf2.toLp f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      simp only [smul_eq_mul, hx]
    _ = ∫ x, s x • (𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 volume) x := hdist
    _ = ∫ x, g x • (𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 volume) x := by
      simp only [hs, Complex.real_smul, smul_eq_mul]

-- Inlined from LOT tree annals_bose_gases (another tree's accepted result):
--   Submission.Obl.BoseGases__restricted_kinetic_domain.integral_norm_sq_L2, obligation o034, Submission/Obl/BoseGases__restricted_kinetic_domain/Plancherel.lean:46-52, lib 487c0679f25d.
--   where it stands there: namespace Submission.Obl.BoseGases__restricted_kinetic_domain | open MeasureTheory FourierTransform | open scoped FourierTransform | variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma integral_norm_sq_L2 (f : Lp (α := V) ℂ 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (L2.inner_def (𝕜 := ℂ) f f)
  simp only [inner_self_eq_norm_sq_to_K] at h
  change (↑(‖f‖) ^ 2 : ℂ).re = (∫ x, (↑(‖f x‖) ^ 2 : ℂ)).re at h
  simp only [← Complex.ofReal_pow, integral_complex_ofReal, Complex.ofReal_re] at h
  exact h.symm

-- Inlined from LOT tree annals_bose_gases (another tree's accepted result):
--   Submission.Obl.BoseGases__restricted_kinetic_domain.integral_norm_sq_fourier, obligation o034, Submission/Obl/BoseGases__restricted_kinetic_domain/Plancherel.lean:54-67, lib 487c0679f25d.
--   where it stands there: namespace Submission.Obl.BoseGases__restricted_kinetic_domain | open MeasureTheory FourierTransform | open scoped FourierTransform | variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma integral_norm_sq_fourier {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ x, ‖(𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 volume) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourier_ae_eq_L2 hf1 hf2] with x hx
      rw [hx]
    _ = ‖𝓕 (hf2.toLp f)‖ ^ 2 := integral_norm_sq_L2 _
    _ = ‖hf2.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖hf2.toLp f x‖ ^ 2 := (integral_norm_sq_L2 _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]

lemma memLp_fourier {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourier_ae_eq_L2 hf1 hf2)).mpr (Lp.memLp _)

end Submission.Obl.k4_oss_flat_decay
