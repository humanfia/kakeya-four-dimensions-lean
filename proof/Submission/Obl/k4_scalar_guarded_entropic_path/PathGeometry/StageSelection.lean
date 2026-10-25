import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageVelocity
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.StagePointRanges
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PathSlices
import Submission.Obl.k4_scalar_guarded_entropic_path.Reference.Exceptions

/-! The finite information window chooses one actual original parent,
with its unchanged world weights and the laws of the same common core. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

structure SelectedWindow (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) where
  index : Fin s.layout.L
  α : ℝ
  alpha_pos : 0 < α
  alpha_two : 2 ≤ s.tangentN j ^ α
  alpha_le : α ≤ δ
  score : (∑ g : Fin (s.windowWorlds j index.val),
      ω (s.candidate index).parent ((s.candidate index).suffixChain.sample j) g *
        Info.rlScore (s.worldLaw pe base j (s.candidateIndex index) g)
          (Info.canonX (s.tangentN j) s.layout.m
            (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))
          (Info.canonY s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))
          (Info.canonZ s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))) ≤
    ((∑ g : Fin (s.windowWorlds j index.val),
      ENNReal.ofReal (ω (s.candidate index).parent ((s.candidate index).suffixChain.sample j) g) *
        s.worldLaw pe base j (s.candidateIndex index) g univ).toReal / 2) *
      Real.log (s.tangentN j ^ α)

theorem eventually_window_selection (s : StagePath ctx source k R δ)
    (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htol : ∀ a, (base a).tolerance = pe.τ)
    (hκ : 0 < ctx.κ) (hκ1 : ctx.κ ≤ 1) (hη : 0 < ctx.η) (hδ : δ ≤ 1)
    (hcost : ∀ᶠ j in atTop, ∀ M : ℕ,
      Real.log (M : ℝ) ≤ ((s.layout.m : ℝ) + 4) * Real.log (s.tangentN j) →
      Info.informationExponent (s.tangentN j)
        (Info.windowCost s.layout.L s.layout.C M 4 (4 ^ (3 * (s.layout.m ^ 2 + 1)))) ≤ δ) :
    ∀ᶠ j in atTop, Nonempty (SelectedWindow s pe base j) := by
  filter_upwards [s.eventually_master_velocity_bins pe base,
    s.eventually_velocity_ambiguities hη al pe base,
    s.eventually_point_range_given_future_nat al pe base htol hκ hκ1 hη hδ,
    s.tangentN_tendsto.eventually_ge_atTop 2, hcost] with j hmaster hv hs hN hcostj
  obtain ⟨Sv, hlog, hSv⟩ := hmaster
  haveI := s.commonMeasure_finite pe base j
  have hC : 1 ≤ s.layout.C := by have := s.layout.coarse_lt; omega
  have hKs : 1 ≤ 4 ^ (3 * (s.layout.m ^ 2 + 1)) :=
    one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
  have hpoint : ∀ a < s.layout.L, ∀ g : Fin (s.windowWorlds j (a + s.layout.C)),
      ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (s.layout.m ^ 2 + 1)) ∧
        ∀ᵐ z ∂s.commonMeasure pe base j,
          s.windowWorld j (a + s.layout.C) z.1 = g →
          Info.canonY s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m)
            (Info.canonX (s.tangentN j) s.layout.m
              (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) (s.windowMap j a z).2) ∈ U := by
    intro a ha
    simpa only [Info.FiniteRangeGiven, Info.canonicalRecord, commonMeasure, tangentN,
      graphK, windowWorlds, windowWorld, windowMap] using hs a ha
  obtain ⟨a, ha, hwin⟩ := Info.exists_window_info (s.commonMeasure pe base j) s.layout.L_pos
    hC measurable_fst (s.windowWorld j)
    (fun a _ g g' h => s.windowWorld_nested j a g g' h)
    (s.windowMap j) (s.measurable_windowMap j)
    (fun a => Filter.Eventually.of_forall (s.windowMap_world j a)) hN s.layout.m
    (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m)
    (s.measurable_masterVelocity j) Sv hSv (by norm_num : 1 ≤ 4) hKs
    (fun a ha g z₀ => hv ⟨a, ha⟩ g z₀) hpoint
  let a₀ : Fin s.layout.L := ⟨a, ha⟩
  let α := Info.informationExponent (s.tangentN j)
    (Info.windowCost s.layout.L s.layout.C (max Sv.card 1) 4 (4 ^ (3 * (s.layout.m ^ 2 + 1))))
  have hα := Info.informationExponent_spec hN
    (Info.windowCost_nonneg (L := s.layout.L) (C := s.layout.C)
      (le_max_right Sv.card 1) (by norm_num : 1 ≤ 4) hKs)
  refine ⟨⟨a₀, α, hα.1, hα.2.1, hcostj _ hlog, ?_⟩⟩
  have hparent := (s.candidate a₀).parent_exact
  have hweight : ∀ g, 0 ≤ ω (s.candidate a₀).parent
      ((s.candidate a₀).suffixChain.sample j) g :=
    (hparent.2.1 ((s.candidate a₀).suffixChain.sample j)).2.1
  have hfinite : ∀ g, IsFiniteMeasure (s.worldLaw pe base j (s.candidateIndex a₀) g) := by
    intro g
    exact Reference.isFiniteMeasure_of_le_mu hparent (s.worldLaw_le pe base j _ g)
  have hslice : ∀ g,
      ENNReal.ofReal (ω (s.candidate a₀).parent ((s.candidate a₀).suffixChain.sample j) g) •
          s.worldLaw pe base j (s.candidateIndex a₀) g =
        ENNReal.ofReal (((s.candidate a₀).suffixChain.originalLaw j univ).toReal) •
          Info.tagSlice (s.commonMeasure pe base j) (s.windowMap j a) g := by
    intro g
    exact Info.weighted_selectedWorldLaw_eq_tagSlice (s.candidate a₀).suffixChain
      s.final_exact j (s.coreSet pe base j) g
  exact hwin _ hweight _ ENNReal.toReal_nonneg _ hfinite hslice

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
