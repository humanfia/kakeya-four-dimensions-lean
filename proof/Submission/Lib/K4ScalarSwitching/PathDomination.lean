/-
Adapted from: here:o062
Original proof: session x0212, commit ce4b105,
Submission/Obl/k4_scalar_mesh_projection/PathDomination.lean.
-/

import Submission.Lib.K4ScalarSwitching.Resampling

namespace Submission.Lib.K4ScalarSwitching

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Extend a history law by a good-transition kernel whose ceiling holds
almost everywhere for that actual history law. Retained paths are not
renormalized and the reference retains the complete history. -/
theorem history_compProd_le_ae {H C : Type*}
    [MeasurableSpace H] [MeasurableSpace C]
    (μ ν : Measure H) [SFinite μ] [SFinite ν]
    (τ : Measure C) [SFinite τ] (κ : Kernel H C) [IsSFiniteKernel κ]
    (K D : ENNReal) (hμ : μ ≤ K • ν) (hκ : ∀ᵐ h ∂μ, κ h ≤ D • τ) :
    μ ⊗ₘ κ ≤ (K * D) • ν.prod τ := by
  have hextend : μ ⊗ₘ κ ≤ D • μ.prod τ := by
    refine Measure.le_iff.mpr ?_
    intro A hA
    rw [Measure.compProd_apply hA, Measure.smul_apply, smul_eq_mul,
      Measure.prod_apply hA]
    calc
      (∫⁻ h, κ h (Prod.mk h ⁻¹' A) ∂μ) ≤
          ∫⁻ h, D * τ (Prod.mk h ⁻¹' A) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hκ] with h hh
        exact Measure.le_iff.mp hh _
          (hA.preimage (measurable_const.prodMk measurable_id))
      _ = D * ∫⁻ h, τ (Prod.mk h ⁻¹' A) ∂μ :=
        lintegral_const_mul D (measurable_measure_prodMk_left hA)
  have hprod := Measure.prod_mono hμ (le_refl τ)
  rw [Measure.prod_smul_left K] at hprod
  calc
    μ ⊗ₘ κ ≤ D • μ.prod τ := hextend
    _ ≤ D • (K • ν.prod τ) := smul_le_smul_left D hprod
    _ = (K * D) • ν.prod τ := by rw [smul_smul, mul_comm D K]

/-- Pointwise form of the full-history extension bound. -/
theorem history_compProd_le {H C : Type*}
    [MeasurableSpace H] [MeasurableSpace C]
    (μ ν : Measure H) [SFinite μ] [SFinite ν]
    (τ : Measure C) [SFinite τ] (κ : Kernel H C) [IsSFiniteKernel κ]
    (K D : ENNReal) (hμ : μ ≤ K • ν) (hκ : ∀ h, κ h ≤ D • τ) :
    μ ⊗ₘ κ ≤ (K * D) • ν.prod τ :=
  history_compProd_le_ae μ ν τ κ K D hμ (ae_of_all μ hκ)

/-- Four successive history-dependent transitions are dominated by the
product palette/time references. All restrictions remain unnormalized;
there is no independence hypothesis after retaining successful paths. -/
theorem four_step_history_law_le_ae {Ω C₀ C₁ C₂ C₃ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C₀] [MeasurableSpace C₁]
    [MeasurableSpace C₂] [MeasurableSpace C₃]
    (μ : Measure Ω) [SFinite μ]
    (τ₀ : Measure C₀) [SFinite τ₀] (τ₁ : Measure C₁) [SFinite τ₁]
    (τ₂ : Measure C₂) [SFinite τ₂] (τ₃ : Measure C₃) [SFinite τ₃]
    (κ₀ : Kernel Ω C₀) [IsSFiniteKernel κ₀]
    (κ₁ : Kernel (Ω × C₀) C₁) [IsSFiniteKernel κ₁]
    (κ₂ : Kernel ((Ω × C₀) × C₁) C₂) [IsSFiniteKernel κ₂]
    (κ₃ : Kernel (((Ω × C₀) × C₁) × C₂) C₃) [IsSFiniteKernel κ₃]
    (D₀ D₁ D₂ D₃ : ENNReal)
    (h₀ : ∀ᵐ h ∂μ, κ₀ h ≤ D₀ • τ₀)
    (h₁ : ∀ᵐ h ∂(μ ⊗ₘ κ₀), κ₁ h ≤ D₁ • τ₁)
    (h₂ : ∀ᵐ h ∂((μ ⊗ₘ κ₀) ⊗ₘ κ₁), κ₂ h ≤ D₂ • τ₂)
    (h₃ : ∀ᵐ h ∂(((μ ⊗ₘ κ₀) ⊗ₘ κ₁) ⊗ₘ κ₂), κ₃ h ≤ D₃ • τ₃) :
    (((μ ⊗ₘ κ₀) ⊗ₘ κ₁) ⊗ₘ κ₂) ⊗ₘ κ₃ ≤
      (D₀ * D₁ * D₂ * D₃) • (((μ.prod τ₀).prod τ₁).prod τ₂).prod τ₃ := by
  have hfirst : μ ⊗ₘ κ₀ ≤ D₀ • μ.prod τ₀ := by
    simpa only [one_mul] using
      history_compProd_le_ae μ μ τ₀ κ₀ 1 D₀ (by simp) h₀
  have hsecond := history_compProd_le_ae (μ ⊗ₘ κ₀) (μ.prod τ₀) τ₁ κ₁ D₀ D₁ hfirst h₁
  have hthird := history_compProd_le_ae ((μ ⊗ₘ κ₀) ⊗ₘ κ₁)
    ((μ.prod τ₀).prod τ₁) τ₂ κ₂ (D₀ * D₁) D₂ hsecond h₂
  exact history_compProd_le_ae (((μ ⊗ₘ κ₀) ⊗ₘ κ₁) ⊗ₘ κ₂)
    (((μ.prod τ₀).prod τ₁).prod τ₂) τ₃ κ₃ (D₀ * D₁ * D₂) D₃ hthird h₃

/-- Pointwise form of the four-transition history-law bound. -/
theorem four_step_history_law_le {Ω C₀ C₁ C₂ C₃ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C₀] [MeasurableSpace C₁]
    [MeasurableSpace C₂] [MeasurableSpace C₃]
    (μ : Measure Ω) [SFinite μ]
    (τ₀ : Measure C₀) [SFinite τ₀] (τ₁ : Measure C₁) [SFinite τ₁]
    (τ₂ : Measure C₂) [SFinite τ₂] (τ₃ : Measure C₃) [SFinite τ₃]
    (κ₀ : Kernel Ω C₀) [IsSFiniteKernel κ₀]
    (κ₁ : Kernel (Ω × C₀) C₁) [IsSFiniteKernel κ₁]
    (κ₂ : Kernel ((Ω × C₀) × C₁) C₂) [IsSFiniteKernel κ₂]
    (κ₃ : Kernel (((Ω × C₀) × C₁) × C₂) C₃) [IsSFiniteKernel κ₃]
    (D₀ D₁ D₂ D₃ : ENNReal)
    (h₀ : ∀ h, κ₀ h ≤ D₀ • τ₀) (h₁ : ∀ h, κ₁ h ≤ D₁ • τ₁)
    (h₂ : ∀ h, κ₂ h ≤ D₂ • τ₂) (h₃ : ∀ h, κ₃ h ≤ D₃ • τ₃) :
    (((μ ⊗ₘ κ₀) ⊗ₘ κ₁) ⊗ₘ κ₂) ⊗ₘ κ₃ ≤
      (D₀ * D₁ * D₂ * D₃) • (((μ.prod τ₀).prod τ₁).prod τ₂).prod τ₃ :=
  four_step_history_law_le_ae μ τ₀ τ₁ τ₂ τ₃ κ₀ κ₁ κ₂ κ₃ D₀ D₁ D₂ D₃
    (ae_of_all μ h₀) (ae_of_all _ h₁) (ae_of_all _ h₂) (ae_of_all _ h₃)

end Submission.Lib.K4ScalarSwitching
