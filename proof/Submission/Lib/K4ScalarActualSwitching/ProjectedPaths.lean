/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9c95a91d9822488d1922a9f04255c7b5bff736aa,
Submission/Obl/k4_scalar_mesh_projection/ProjectedPaths.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.RestrictedRefresh

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- A transition may depend on the complete history, even when the
observed history is shorter. Its conditional ceiling still propagates the
observed product bound, without a Markov assumption for the observations. -/
theorem projected_history_compProd_le_ae {H Z Y C : Type*}
    [MeasurableSpace H] [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace C]
    (θ : Measure H) [SFinite θ] (ν : Measure Z) [SFinite ν]
    (τ : Measure C) [SFinite τ] (κ : Kernel H Y) [IsSFiniteKernel κ]
    (past : H → Z) (hpast : Measurable past)
    (next : Y → C) (hnext : Measurable next) (K D : ENNReal)
    (hθ : θ.map past ≤ K • ν)
    (hκ : ∀ᵐ h ∂θ, (κ h).map next ≤ D • τ) :
    (θ ⊗ₘ κ).map (Prod.map past next) ≤ (K * D) • ν.prod τ := by
  have hmap : (θ ⊗ₘ κ).map (Prod.map past next) =
      (θ ⊗ₘ κ.map next).map (Prod.map past id) := by
    rw [Measure.compProd_map hnext, Measure.map_map (hpast.prodMap measurable_id)
      (measurable_id.prodMap hnext)]
    rfl
  rw [hmap]
  apply joint_control_time_transition_le_ae θ ν τ (κ.map next) past hpast K D hθ
  simpa only [Kernel.map_apply _ hnext] using hκ

/-- Four actual transitions may retain arbitrary successful subsets of
their complete incidence histories. The observed start/control/time law
remains dominated by the original product reference. -/
theorem projected_four_step_retained_law_le {Ω C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (τ : Measure C) [SFinite τ]
    (κ₀ : Kernel Ω Ω) [IsFiniteKernel κ₀]
    (κ₁ : Kernel (Ω × Ω) Ω) [IsFiniteKernel κ₁]
    (κ₂ : Kernel ((Ω × Ω) × Ω) Ω) [IsFiniteKernel κ₂]
    (κ₃ : Kernel (((Ω × Ω) × Ω) × Ω) Ω) [IsFiniteKernel κ₃]
    (next : Ω → C) (hnext : Measurable next)
    (G₀ : Set (Ω × Ω)) (G₁ : Set ((Ω × Ω) × Ω))
    (G₂ : Set (((Ω × Ω) × Ω) × Ω)) (G₃ : Set ((((Ω × Ω) × Ω) × Ω) × Ω))
    (D₀ D₁ D₂ D₃ : ENNReal) :
    let θ₁ := (μ ⊗ₘ κ₀).restrict G₀
    let θ₂ := (θ₁ ⊗ₘ κ₁).restrict G₁
    let θ₃ := (θ₂ ⊗ₘ κ₂).restrict G₂
    let θ₄ := (θ₃ ⊗ₘ κ₃).restrict G₃
    (∀ᵐ h ∂μ, (κ₀ h).map next ≤ D₀ • τ) →
    (∀ᵐ h ∂θ₁, (κ₁ h).map next ≤ D₁ • τ) →
    (∀ᵐ h ∂θ₂, (κ₂ h).map next ≤ D₂ • τ) →
    (∀ᵐ h ∂θ₃, (κ₃ h).map next ≤ D₃ • τ) →
    θ₄.map (Prod.map (Prod.map (Prod.map (Prod.map id next) next) next) next) ≤
      (D₀ * D₁ * D₂ * D₃) • (((μ.prod τ).prod τ).prod τ).prod τ := by
  let θ₁ := (μ ⊗ₘ κ₀).restrict G₀
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁]; infer_instance
  let θ₂ := (θ₁ ⊗ₘ κ₁).restrict G₁
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂]; infer_instance
  let θ₃ := (θ₂ ⊗ₘ κ₂).restrict G₂
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃]; infer_instance
  let θ₄ := (θ₃ ⊗ₘ κ₃).restrict G₃
  let f₁ : Ω × Ω → Ω × C := Prod.map id next
  let f₂ : (Ω × Ω) × Ω → (Ω × C) × C := Prod.map f₁ next
  let f₃ : ((Ω × Ω) × Ω) × Ω → ((Ω × C) × C) × C := Prod.map f₂ next
  let f₄ : (((Ω × Ω) × Ω) × Ω) × Ω → (((Ω × C) × C) × C) × C := Prod.map f₃ next
  have hf₁ : Measurable f₁ := measurable_id.prodMap hnext
  have hf₂ : Measurable f₂ := hf₁.prodMap hnext
  have hf₃ : Measurable f₃ := hf₂.prodMap hnext
  have hf₄ : Measurable f₄ := hf₃.prodMap hnext
  change (∀ᵐ h ∂μ, (κ₀ h).map next ≤ D₀ • τ) →
    (∀ᵐ h ∂θ₁, (κ₁ h).map next ≤ D₁ • τ) →
    (∀ᵐ h ∂θ₂, (κ₂ h).map next ≤ D₂ • τ) →
    (∀ᵐ h ∂θ₃, (κ₃ h).map next ≤ D₃ • τ) →
    θ₄.map f₄ ≤ (D₀ * D₁ * D₂ * D₃) • (((μ.prod τ).prod τ).prod τ).prod τ
  intro h₀ h₁ h₂ h₃
  have hh₀ := projected_history_compProd_le_ae μ μ τ κ₀ id measurable_id next hnext 1 D₀
    (by simp) h₀
  have hθ₁ : θ₁.map f₁ ≤ D₀ • μ.prod τ := by
    exact (Measure.map_mono Measure.restrict_le_self hf₁).trans (by simpa only [one_mul] using hh₀)
  have hh₁ := projected_history_compProd_le_ae θ₁ (μ.prod τ) τ κ₁ f₁ hf₁ next hnext
    D₀ D₁ hθ₁ h₁
  have hθ₂ : θ₂.map f₂ ≤ (D₀ * D₁) • (μ.prod τ).prod τ :=
    (Measure.map_mono Measure.restrict_le_self hf₂).trans hh₁
  have hh₂ := projected_history_compProd_le_ae θ₂ ((μ.prod τ).prod τ) τ κ₂ f₂ hf₂ next hnext
    (D₀ * D₁) D₂ hθ₂ h₂
  have hθ₃ : θ₃.map f₃ ≤ (D₀ * D₁ * D₂) • ((μ.prod τ).prod τ).prod τ :=
    (Measure.map_mono Measure.restrict_le_self hf₃).trans hh₂
  have hh₃ := projected_history_compProd_le_ae θ₃ (((μ.prod τ).prod τ).prod τ) τ κ₃
    f₃ hf₃ next hnext (D₀ * D₁ * D₂) D₃ hθ₃ h₃
  exact (Measure.map_mono Measure.restrict_le_self hf₄).trans hh₃

end Submission.Lib.K4ScalarActualSwitching
