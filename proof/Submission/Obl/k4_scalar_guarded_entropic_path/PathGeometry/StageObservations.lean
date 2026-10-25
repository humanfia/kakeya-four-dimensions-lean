import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCore
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SupportBounds
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.VelocityReadouts
import Submission.Obl.k4_scalar_guarded_entropic_path.MasterVelocity
import Submission.Obl.k4_scalar_guarded_entropic_path.WindowBudget

/-! The measured window uses the actual suffix maps of the one chosen
path, at their literal original samples and on the same retained law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

abbrev CommonState (s : StagePath ctx source k R δ) (j : ℕ) := Fin (W s.final j) × State

def tangentN (s : StagePath ctx source k R δ) (j : ℕ) : ℝ := N s.final j ^ s.layout.scale
def graphK (s : StagePath ctx source k R δ) (j : ℕ) : ℝ := N s.final j ^ (s.layout.scale / 1000)

def commonMeasure (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    Measure (s.CommonState j) := (normalizedWorldMixture s.final j).restrict (s.coreSet pe base j)

def windowWorlds (s : StagePath ctx source k R δ) (j a : ℕ) : ℕ :=
  W (s.view (a + 1)).parent ((s.view (a + 1)).suffixChain.sample j)

def windowWorld (s : StagePath ctx source k R δ) (j a : ℕ) :
    Fin (W s.final j) → Fin (s.windowWorlds j a) := (s.view (a + 1)).suffixChain.world j

def windowMap (s : StagePath ctx source k R δ) (j a : ℕ) :
    s.CommonState j → Fin (s.windowWorlds j a) × State := (s.view (a + 1)).suffixChain.pullback j

def masterVelocity (s : StagePath ctx source k R δ) (j : ℕ) (z : s.CommonState j) : ℤ :=
  velocityBin (s.tangentN j) ((s.layout.m : ℝ) + 2) (s.path.velocityAt s.outer s.certs j 0 z)

theorem tangentN_ge_one (s : StagePath ctx source k R δ) (j : ℕ) : 1 ≤ s.tangentN j :=
  Real.one_le_rpow ((by norm_num : (1 : ℝ) ≤ 2).trans (s.final_exact.1.1 j)) s.layout.scale_pos.le

theorem tangentN_tendsto (s : StagePath ctx source k R δ) : Tendsto s.tangentN atTop atTop :=
  (tendsto_rpow_atTop s.layout.scale_pos).comp s.final_exact.1.2.1

theorem graphK_ge_one (s : StagePath ctx source k R δ) (j : ℕ) : 1 ≤ s.graphK j :=
  Real.one_le_rpow ((by norm_num : (1 : ℝ) ≤ 2).trans (s.final_exact.1.1 j))
    (div_nonneg s.layout.scale_pos.le (by norm_num))

theorem graphK_le_tangentN (s : StagePath ctx source k R δ) (j : ℕ) : s.graphK j ≤ s.tangentN j :=
  Real.rpow_le_rpow_of_exponent_le
    ((by norm_num : (1 : ℝ) ≤ 2).trans (s.final_exact.1.1 j)) (by linarith [s.layout.scale_pos])

theorem commonMeasure_finite (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    IsFiniteMeasure (s.commonMeasure pe base j) := by
  letI := normalizedWorldMixture_isProbability s.final_exact j
  change IsFiniteMeasure ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
  infer_instance

theorem commonMeasure_ac (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    s.commonMeasure pe base j ≪ worldMixture s.final j :=
  (Measure.absolutelyContinuous_of_le (show s.commonMeasure pe base j ≤
    normalizedWorldMixture s.final j from Measure.restrict_le_self)).trans
      Measure.smul_absolutelyContinuous

theorem measurable_windowMap (s : StagePath ctx source k R δ) (j a : ℕ) :
    Measurable (s.windowMap j a) := (s.view (a + 1)).suffixChain.measurable_pullback j

theorem windowMap_world (s : StagePath ctx source k R δ) (j a : ℕ) (z : s.CommonState j) :
    (s.windowMap j a z).1 = s.windowWorld j a z.1 :=
  (s.view (a + 1)).suffixChain.pullback_world j z

theorem windowWorld_nested (s : StagePath ctx source k R δ) (j a : ℕ)
    (g g' : Fin (W s.final j)) (h : s.windowWorld j (a + 1) g = s.windowWorld j (a + 1) g') :
    s.windowWorld j a g = s.windowWorld j a g' :=
  s.path.viewAt_world_nested s.outer s.certs s.laws _ (a + 1) j g g' h

theorem measurable_masterVelocity (s : StagePath ctx source k R δ) (j : ℕ) :
    Measurable (s.masterVelocity j) := by
  have h := (Info.measurable_velocityBin_coord (s.tangentN j) ((s.layout.m : ℝ) + 2)).comp
    (measurable_snd.comp ((s.path.measuredChain s.outer s.certs).measurable_pullback j))
  change Measurable (fun z : s.CommonState j => velocityBin (s.tangentN j)
    ((s.layout.m : ℝ) + 2) (s.path.velocityAt s.outer s.certs j 0 z))
  simpa only [s.path.velocityAt_zero, Function.comp_def, CommonState, final] using h

theorem window_bounded_ae (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : Fin s.layout.L)
    (hK : K (s.candidate a).parent ((s.candidate a).suffixChain.sample j) ≤ s.graphK j) :
    ∀ᵐ z ∂s.commonMeasure pe base j,
      (s.windowMap j a.val z).2.2 ∈ Icc (0 : ℝ) 1 ∧
        ∀ e, |(s.windowMap j a.val z).2.1.2 e| ≤ s.graphK j := by
  have hb := (s.candidate a).suffixChain.pullback_bounded_ae (s.candidate a).parent_exact j
    (s.commonMeasure pe base j) (s.commonMeasure_ac pe base j)
  filter_upwards [hb] with z hz
  exact ⟨hz.1, fun e => (hz.2 e).trans hK⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
