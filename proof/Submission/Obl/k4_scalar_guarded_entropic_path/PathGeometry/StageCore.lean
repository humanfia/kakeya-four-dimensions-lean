import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StagePath
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FiniteViewBudgets
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CoreViews
import Submission.Obl.k4_scalar_guarded_entropic_path.StageExponents

/-! All candidate laws are fixed pullbacks of one prepared quarter
core. Their original priors, weights and tested density caps remain exact. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

abbrev ViewIndex (s : StagePath ctx source k R δ) := Fin (s.layout.targets.length + 1)

def densityTests (s : StagePath ctx source k R δ)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) :
    (a : s.ViewIndex) → DensityTests (s.views a).parent :=
  fun a => (s.views a).withLayerTests (base a)

def coreSet (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    Set (Fin (W s.final j) × State) :=
  PreparedViews.flooredCore s.views (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) pe.γ j

def worldLaw (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : s.ViewIndex) :
    Fin (W (s.views a).parent ((s.views a).suffixChain.sample j)) → Measure State :=
  (s.views a).suffixChain.selectedWorldLaw j (s.coreSet pe base j)

theorem measurableSet_coreSet (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    MeasurableSet (s.coreSet pe base j) :=
  PreparedViews.measurableSet_flooredCore _ _ _ _ _ _

theorem coreSet_subset_prepared (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    s.coreSet pe base j ⊆
      PreparedViews.core s.views (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) j :=
  PreparedViews.flooredCore_subset_core _ _ _ _ _ _

theorem core_restrict_le_prepared (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) :
    (normalizedWorldMixture s.final j).restrict (s.coreSet pe base j) ≤
      (normalizedWorldMixture s.final j).restrict
        (PreparedViews.core s.views (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) j) :=
  Measure.restrict_mono (s.coreSet_subset_prepared pe base j) le_rfl

theorem eventually_core_properties (s : StagePath ctx source k R δ) (hη : 0 < ctx.η) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) :
    ∀ᶠ j in atTop, PreparedViews.FlooredCoreProperties s.views
      (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) pe.γ j (s.coreSet pe base j) := by
  apply PreparedViews.eventually_flooredCore_properties s.views s.final_exact
    (s.path.measuredChain s.outer s.certs) s.views_referenceFactor
    (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base)
    (fun _ => pe.ε_pos) (fun _ => pe.u_pos) _ _ pe.γ pe.γ_pos
  · intro a
    have hL := s.view_length a.val
    change (1 / 2 : ℝ) < L (s.views a).parent at hL
    have hU : ctx.η / 2 < U (s.views a).parent := by
      rw [(s.views a).range]
      nlinarith only [hL, hη]
    exact pe.u_angular.trans hU.le
  · intro a
    simpa only [(s.views a).angular] using pe.ε_width

theorem worldLaw_le (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : s.ViewIndex)
    (g : Fin (W (s.views a).parent ((s.views a).suffixChain.sample j))) :
    s.worldLaw pe base j a g ≤ mu (s.views a).parent ((s.views a).suffixChain.sample j) g :=
  (s.views a).suffixChain.selectedWorldLaw_le s.final_exact j _ g

theorem core_pure_null (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : s.ViewIndex)
    (r : ℝ) (hr : r ∈ (s.densityTests base a).pure)
    (g : Fin (W (s.views a).parent ((s.views a).suffixChain.sample j))) :
    s.worldLaw pe base j a g (pureException (s.views a).parent ((s.views a).suffixChain.sample j)
      g r (base a).tolerance) = 0 := by
  exact PreparedViews.current_pure_null s.views (fun _ => pe.ε) (fun _ => pe.u)
    (s.densityTests base) j ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
    (s.core_restrict_le_prepared pe base j) a r hr g

theorem core_angular_null (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : s.ViewIndex)
    (b : ℝ) (hb : b ∈ (base a).angular)
    (g : Fin (W (s.views a).parent ((s.views a).suffixChain.sample j))) :
    s.worldLaw pe base j a g (angularException (s.views a).parent ((s.views a).suffixChain.sample j)
      g b (base a).tolerance) = 0 := by
  exact PreparedViews.current_angular_null s.views (fun _ => pe.ε) (fun _ => pe.u)
    (s.densityTests base) j ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
    (s.core_restrict_le_prepared pe base j) a b hb g

theorem core_narrow_null (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (a : s.ViewIndex)
    (ℓ : Fin (s.views a).count)
    (g : Fin (W (s.views a).parent ((s.views a).suffixChain.sample j))) :
    s.worldLaw pe base j a g (WidthGeometry.narrowEvent
      ((s.views a).layerAt pe.ε ℓ j) pe.ε pe.u g) = 0 := by
  exact PreparedViews.current_narrow_null s.views (fun _ => pe.ε) (fun _ => pe.u)
    (s.densityTests base) j ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
    (s.core_restrict_le_prepared pe base j) a ℓ g

theorem worldLaw_mass_subpower (s : StagePath ctx source k R δ) (hη : 0 < ctx.η) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ j in atTop, ∀ a : s.ViewIndex, ENNReal.ofReal (N s.final j ^ (-τ)) ≤
      ∑ g, ENNReal.ofReal (ω (s.views a).parent ((s.views a).suffixChain.sample j) g) *
        s.worldLaw pe base j a g univ := by
  have hmass : ∀ᶠ j in atTop, ENNReal.ofReal (1 / 4 : ℝ) ≤
      normalizedWorldMixture s.final j (s.coreSet pe base j) :=
    (s.eventually_core_properties hη pe base).mono fun _ hj => hj.2.2.1
  apply Filter.eventually_all.2
  intro a
  exact (s.views a).suffixChain.selectedWorldLaw_mass_subpower_of_fixed_fraction s.final_exact
    (s.coreSet pe base) (1 / 4) (by norm_num) hmass τ hτ

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
