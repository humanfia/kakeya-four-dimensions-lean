import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalCount
import Submission.Lib.K4ParentSignalPreparation.NativeBranchGroups

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open scoped ENNReal

noncomputable section

def parentBranch (P0 : Po) (e : Ev) : Bool :=
  if 0 < eval (xp e.1 e.2) (pderiv 3 P0) then true else false

theorem measurable_parentBranch (P0 : Po) : Measurable (parentBranch P0) := by
  have hpos : MeasurableSet {e : Ev | 0 < packetSignal (pderiv 3 P0) e} :=
    measurableSet_lt measurable_const (measurable_packetSignal _)
  exact measurable_const.piecewise hpos measurable_const

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln} {B a ζ d : ℝ} {c u : P2} {P0 : Po}
  {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

def interceptBin (w : ℝ) (e : Ev) : ℤ :=
  ⌊(ownIntercept T j c u P0 source.Pot e.1/a)/w⌋

theorem measurable_interceptBin (w : ℝ) : Measurable (source.interceptBin w) :=
  Int.measurable_floor.comp (((measurable_ownIntercept T j c u P0 source.Pot).comp
    measurable_fst).div_const a |>.div_const w)

theorem finite_intercept_catalogue
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hresolve : countingResolution source.K (physicalPotentialLip q source.K)*ζ ≤ w) :
    ∃ catalogue : Finset ℤ, ∀ e ∈ source.S, source.interceptBin w e ∈ catalogue := by
  have hK0 : 0 < source.K := by linarith [source.K_two]
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  let Hlip := physicalPotentialLip q source.K
  have hHlip : 0 ≤ Hlip := physicalPotentialLip_nonneg q hK0.le
  let p := physicalCountingMesh a ((2:ℝ)^T)⁻¹ w source.K Hlip
  rcases physical_counting_mesh_spec source.a_pos hh hw hw1 hK0.le hHlip
      source.ε_pos hζ source.ε_le source.ε_clock hresolve with
    ⟨hp, hεp, hpw, hp1, hεw, hζw, hLipmesh, hPhysicalMesh, hsmall⟩
  have hcensus := source.census p w hεp hp1 hεw hw1 hPhysicalMesh
  obtain ⟨hfinite, hcount⟩ := intercept_pair_census source.S
    (fun e i => packetBase T j c u e i) (fun e => packetSignal P0 e/a)
    (fun e => ownIntercept T j c u P0 source.Pot e.1/a)
    (fun z => eval z source.Pot/a) p w ζ (Hlip*((2:ℝ)^T)⁻¹/a)
    hp hw (div_nonneg (mul_nonneg hHlip hh.le) source.a_pos.le) hζw hLipmesh
    (source.normalized_fit_at_source_event hSA) source.potential_lipschitz hcensus.1
  refine ⟨hfinite.toFinset.image Prod.fst, ?_⟩
  intro e he
  apply Finset.mem_image.mpr
  refine ⟨(source.interceptBin w e, fun i => ⌊packetBase T j c u e i/p⌋), ?_, rfl⟩
  exact hfinite.mem_toFinset.mpr ⟨e, he, rfl⟩

theorem intercept_bins_close
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {w : ℝ} (hw : 0 < w)
    (hresolve : countingResolution source.K (physicalPotentialLip q source.K)*ζ ≤ w)
    {e f : Ev} (he : e ∈ source.S) (hf : f ∈ source.S)
    (hstate : physicalCode (packetBase T j c u) (fun e => packetSignal P0 e/a) source.ε e =
      physicalCode (packetBase T j c u) (fun e => packetSignal P0 e/a) source.ε f) :
    source.interceptBin w e ∈ Icc (source.interceptBin w f - 2) (source.interceptBin w f + 2) := by
  have hK0 : 0 < source.K := by linarith [source.K_two]
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  have hH : 0 ≤ physicalPotentialLip q source.K := physicalPotentialLip_nonneg q hK0.le
  have hD : 3+3*physicalPotentialLip q source.K ≤
      countingResolution source.K (physicalPotentialLip q source.K) := by
    unfold countingResolution
    linarith [pow_nonneg hK0.le 100]
  have hsmall : (3+3*physicalPotentialLip q source.K)*ζ ≤ 2*w :=
    ((mul_le_mul_of_nonneg_right hD hζ.le).trans hresolve).trans (by linarith)
  have hclose := Submission.Lib.K4ParentSignalPreparation.BranchGroups.physical_intercept_bins_close_of_clock_mesh
    source.S (fun e i => packetBase T j c u e i) (packetSignal P0)
    (fun e => ownIntercept T j c u P0 source.Pot e.1) source.Pot
    source.a_pos hh source.ε_pos (by linarith [source.K_two]) hw hH
    source.coordinate_bound (source.fit_at_source_event hSA)
    (physical_potential_coefficient_lip q source.Pot source.degree
      (by linarith [source.K_two]) hh.le source.coeff)
    source.ε_le source.ε_clock hsmall he hf hstate
  simpa only [interceptBin, div_div] using hclose

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
