import Submission.Obl.k4_physical_parent_potential_candidates.SourceLines
import Submission.Obl.k4_physical_parent_potential_candidates.CountingMesh
import Submission.Obl.k4_physical_parent_potential_candidates.CountGroups

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4ContinuousKakeya
open scoped ENNReal

noncomputable section

/-- Specialize the entire MK3 group count to the actual frozen physical
packet witnesses. The old chart is used only to locate the original source. -/
theorem physical_source_heavy_bin
    {q T j : ℕ} {ν : Measure Ln} [IsFiniteMeasure ν]
    {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
    (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {C w : ℝ} (hC : 0 < C) (hMK : FiniteMK 3 C)
    (hw : 0 < w) (hw1 : w ≤ 1)
    (hresolve : countingResolution source.K (physicalPotentialLip q source.K)*ζ ≤ w) :
    ∃ g : ℤ,
      ((2:ℝ)^T)⁻¹*ν.real A *
          ((source.K^(-100:ℝ))^2/(1+source.K)^3/8)*w^d /
        (7962624*(1000*C)^2*source.K^5) ≤
      ((ν.prod volume).restrict source.S).real
        {e | ⌊(ownIntercept T j c u P0 source.Pot e.1/a)/w⌋ = g} := by
  have hK0 : 0 < source.K := by linarith [source.K_two]
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  let Hlip := physicalPotentialLip q source.K
  have hHlip : 0 ≤ Hlip := physicalPotentialLip_nonneg q hK0.le
  let p := physicalCountingMesh a ((2:ℝ)^T)⁻¹ w source.K Hlip
  have hmesh := physical_counting_mesh_spec source.a_pos hh hw hw1 hK0.le hHlip
    source.ε_pos hζ source.ε_le source.ε_clock hresolve
  rcases hmesh with ⟨hp, hεp, hpw, hp1, hεw, hζw, hLipmesh, hPhysicalMesh, hsmall⟩
  have hcensus := source.census p w hεp hp1 hεw hw1 hPhysicalMesh
  have hsub := source.positive_events_subset
  have hcodeSub : {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ source.positiveEvents,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k} ⊆
      {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ source.S,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k} := by
    rintro k ⟨e, he, hk⟩
    exact ⟨e, hsub he, hk⟩
  have hcensusFinite := hcensus.1.subset hcodeSub
  have hcensusCount : (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ source.positiveEvents,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k}).ncard:ℝ) ≤
      source.K/(p^3*w^d) :=
    (show (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ source.positiveEvents,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k}).ncard:ℝ) ≤
      (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ source.S,
      ((fun i => ⌊packetBase T j c u e i/p⌋), ⌊(packetSignal P0 e/a)/w⌋) = k}).ncard:ℝ) by
      exact_mod_cast Set.ncard_le_ncard hcodeSub hcensus.1).trans hcensus.2
  have hpol : ∀ e ∈ source.positiveEvents, ∀ f ∈ source.positiveEvents,
      |eval (fun i => packetBase T j c u e i) source.Pot/a -
        eval (fun i => packetBase T j c u f i) source.Pot/a| ≤
      (Hlip*((2:ℝ)^T)⁻¹/a) *
        ‖(fun i => packetBase T j c u e i) - (fun i => packetBase T j c u f i)‖ := by
    intro e he f hf
    exact physical_potential_lipschitz q source.Pot source.degree
      (by linarith [source.K_two]) hh.le source.a_pos source.coeff
      _ _ (source.coordinate_bound e (hsub he)) (source.coordinate_bound f (hsub hf))
  have hstrip : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict source.positiveEvents)
        {e | ((fun i => ⌊packetBase T j c u e i/source.ε⌋),
          ⌊(packetSignal P0 e/a)/source.ε⌋) = k ∧
          |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ≤
      ENNReal.ofReal ((1:ℝ)/1000000000000) *
        ((ν.prod volume).restrict source.positiveEvents)
          {e | ((fun i => ⌊packetBase T j c u e i/source.ε⌋),
            ⌊(packetSignal P0 e/a)/source.ε⌋) = k} := by
    intro k n t hn
    rw [source.positive_events_law]
    have hnum : ENNReal.ofReal ((1:ℝ)/1000000000000) = (1/1000000000000:ENNReal) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    simpa only [physicalCode, hnum] using source.breadth k n t hn
  obtain ⟨g, hg⟩ := exists_original_heavy_intercept_bin ν source.lineSet A
    source.measurable_lineSet (source.lineSet_subset (fun e he => (hSA he).1))
    ((2:ℝ)^T)⁻¹ ((j:ℝ)*((2:ℝ)^T)⁻¹) source.ε p w ζ
    (Hlip*((2:ℝ)^T)⁻¹/a) source.K (source.K^(-100:ℝ)) C d
    hh source.ε_pos hp hw hεp hεw hζw
    (div_nonneg (mul_nonneg hHlip hh.le) source.a_pos.le) hLipmesh source.K_two
    (Real.rpow_pos_of_pos hK0 _) hC hMK source.reference_prior_pos
    (packetOrigin T j c u) v (measurable_packetOrigin T j c u) measurable_velocity
    (3*source.K) (by positivity) (source.line_origin hSA) source.line_velocity
    (packetBase T j c u) (measurable_packetBase T j c u)
    (fun _ => rfl) (packetBase_affine T j c u)
    (fun e => packetSignal P0 e/a) ((measurable_packetSignal P0).div_const a)
    (fun l => ownIntercept T j c u P0 source.Pot l/a)
    ((measurable_ownIntercept T j c u P0 source.Pot).div_const a)
    (fun x => eval x source.Pot/a) source.positiveEvents source.measurable_positiveEvents
    (source.positive_events_support hSA) (source.positive_events_mass_floor hSA)
    (source.normalized_fit_at_event hSA) hpol hstrip hcensusFinite hcensusCount
  refine ⟨g, ?_⟩
  rw [source.positive_events_law] at hg
  exact hg

end

end Submission.Obl.k4_physical_parent_potential_candidates
