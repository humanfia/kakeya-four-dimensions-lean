import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointWindowFromCore
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.StageOriginalBlocks
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointEnvelope
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCore

/-! The concrete finite-stage common law satisfies the point ambiguity
input of the information-window theorem for every candidate at once. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures TrueLiftChains Info
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

/-- Every candidate's complete canonical point record has constant
ambiguity given its actual C-th future original world, on one common
prepared quarter core. -/
theorem eventually_point_range_given_future (s : StagePath ctx source k R δ)
    (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htol : ∀ a, (base a).tolerance = pe.τ)
    (hκ : 0 < ctx.κ) (hκ1 : ctx.κ ≤ 1) (hη : 0 < ctx.η) (hδ : δ ≤ 1) :
    ∀ᶠ j in atTop, ∀ a : Fin s.layout.L,
      FiniteRangeGiven ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
        (fun z => canonicalRecord (N s.final j ^ s.layout.scale)
          (N s.final j ^ (s.layout.scale / 1000)) s.layout.m
          (((s.candidate a).suffixChain.pullback j z).2))
        (fun z => (s.view (a.val + 1 + s.layout.C)).suffixChain.world j z.1)
        (4 ^ (3 * (s.layout.m ^ 2 + 1))) := by
  have hscale := s.layout.scale_pos
  have hδpos : 0 < δ := hscale.trans_le s.layout.scale_error
  have hN : ∀ j, 1 ≤ N s.final j := fun j =>
    (by norm_num : (1 : ℝ) ≤ 2).trans (s.final_exact.1.1 j)
  have henv := eventually_pointEnvelope hN s.final_exact.1.2.1 hscale al.v_pos al.v_scale
    pe.ε_small pe.γ_small pe.width_gap pe.τ_scale
  have hvcal : s.layout.scale * δ / 100 ≤ s.layout.scale / 8 := by
    nlinarith only [mul_le_mul_of_nonneg_left hδ hscale.le, hscale]
  have herror : 0 ≤ s.layout.scale * δ / 10000 := by positivity
  have herrorSmall : s.layout.scale * δ / 10000 ≤ s.layout.scale / 8 := by
    have hp : 0 < s.layout.scale * δ := by positivity
    linarith only [hvcal, hp]
  filter_upwards [s.eventually_core_properties hη pe base,
    s.eventually_original_geometry_blocks al pe, henv] with j hcore hblocks hg
  intro a
  let a₀ := s.candidateIndex a
  have hc : s.layout.C ≤ (s.views a₀).count := s.candidate_count a
  let c := layoutPointCoarse s.layout hc
  let f := layoutPointFine s.layout hc
  obtain ⟨Qc, hcChoice, hcGeom, hcFloor⟩ := hcore.2.2.2.1 a₀ c
  obtain ⟨Qf, hfChoice, hfGeom, hfFloor⟩ := hcore.2.2.2.1 a₀ f
  have hcoarse := (hblocks a₀ c Qc hcGeom).2
  have hfine := (hblocks a₀ f Qf hfGeom).1
  have htest : (s.views a₀).depth c ∈ (s.densityTests base a₀).pure :=
    (s.views a₀).layer_mem_withLayerTests (base a₀) c
  have hpure : N s.final j ^ (s.densityTests base a₀).tolerance ≤
      N s.final j ^ (s.layout.scale / 1000) := by
    change N s.final j ^ (base a₀).tolerance ≤ _
    rw [htol]
    exact hg.pure
  have hlocal := canonical_point_ranges_from_layout_core s.views s.final_exact
    (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) pe.γ j (s.coreSet pe base j) hcore
    a₀ (s.path.viewAtReadouts s.outer s.certs s.laws (.nil _ (source.angular s.outer).1)
      (a.val + 1)) s.layout hc (N s.final j ^ (s.layout.scale / 1000))
    (s.layout.scale * δ / 10000) (s.layout.scale * δ / 100)
    (N s.final j ^ (s.layout.scale * δ / 100))
    hg.one hκ hκ1 herror herrorSmall hvcal (s.grids (a.val + 1)) pe.ε_pos.le
    htest hg.fit hg.floor hg.width hpure
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hN j)) _) le_rfl hcoarse hfine hg.margin
  exact finiteRangeGiven_viewAt_future s.path s.outer s.certs s.laws
    (.nil _ (source.angular s.outer).1) (a.val + 1) j s.layout.C
    ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j)) _ _ hlocal

/-- Natural candidate indices, with the future index written in the
literal form obtained by applying the common menu at `a + C`. -/
theorem eventually_point_range_given_future_nat (s : StagePath ctx source k R δ)
    (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htol : ∀ a, (base a).tolerance = pe.τ)
    (hκ : 0 < ctx.κ) (hκ1 : ctx.κ ≤ 1) (hη : 0 < ctx.η) (hδ : δ ≤ 1) :
    ∀ᶠ j in atTop, ∀ a : ℕ, a < s.layout.L →
      FiniteRangeGiven ((normalizedWorldMixture s.final j).restrict (s.coreSet pe base j))
        (fun z => canonicalRecord (N s.final j ^ s.layout.scale)
          (N s.final j ^ (s.layout.scale / 1000)) s.layout.m
          (((s.view (a + 1)).suffixChain.pullback j z).2))
        (fun z => (s.view (a + s.layout.C + 1)).suffixChain.world j z.1)
        (4 ^ (3 * (s.layout.m ^ 2 + 1))) := by
  filter_upwards [s.eventually_point_range_given_future al pe base htol hκ hκ1 hη hδ]
    with j hj a ha
  have hh := hj ⟨a, ha⟩
  dsimp only [candidate] at hh
  rw [Nat.add_right_comm a 1 s.layout.C] at hh
  exact hh

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
