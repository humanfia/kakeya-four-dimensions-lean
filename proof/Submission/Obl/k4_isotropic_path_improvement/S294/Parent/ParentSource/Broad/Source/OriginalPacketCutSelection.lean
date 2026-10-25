-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalPacketCutSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalPacketCutSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalPacketCutSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DensePackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_scalar_grid_cartesian_field.HeavyCells

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal BigOperators

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
    {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Per-parent cuts paid by the full original assignment and clock select
one original parent with the same relative density. The unit packet budget
removes every dependence on the number of packets and on their masses. -/
theorem Native.PathData.Valid.exists_dense_original_packet_after_cuts
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hsum : ∑ w, ω w=1)
    {I : Type*} [Fintype I] (node : I → Fin p.C) (hinj : Function.Injective node)
    (level : ℕ) (hlevel : ∀ b, p.lev (node b)=level)
    (source : Fin W → Set Ev)
    (hcover : ∀ w, source w⊆{z | ∃ b, p.γ (node b)=w ∧ z∈p.F (node b)})
    (kept : I → Set Ev) (hsub : ∀ b, kept b⊆source (p.γ (node b))∩p.F (node b))
    (cost : ENNReal)
    (hloss : ∀ b, ((ν (p.γ (node b))).prod volume) (source (p.γ (node b))∩p.F (node b)) ≤
      ((ν (p.γ (node b))).prod volume) (kept b)+
        cost*(ν (p.γ (node b)) (p.A (node b))*ENNReal.ofReal (((2:ℝ)^p.T level)⁻¹)))
    {density : ℝ} (hdensity : 0 < density)
    (hmass : ENNReal.ofReal density+ENNReal.ofReal density ≤
      ∑ w, ENNReal.ofReal (ω w)*((ν w).prod volume) (source w))
    (hcost : cost ≤ ENNReal.ofReal density) :
    ∃ b : I, 0 < ω (p.γ (node b)) ∧ ν (p.γ (node b)) (p.A (node b))≠0 ∧
      ENNReal.ofReal density*
        (ν (p.γ (node b)) (p.A (node b))*ENNReal.ofReal (((2:ℝ)^p.T level)⁻¹)) ≤
          ((ν (p.γ (node b))).prod volume) (kept b) := by
  classical
  let full := fun b : I => p.A (node b) ×ˢ Icc
    ((p.j (node b):ℝ)/(2:ℝ)^p.T level) (((p.j (node b):ℝ)+1)/(2:ℝ)^p.T level)
  let reference := fun b : I => ν (p.γ (node b)) (p.A (node b))*
    ENNReal.ofReal (((2:ℝ)^p.T level)⁻¹)
  let mass := fun b : I => ((ν (p.γ (node b))).prod volume) (kept b)
  have hfull (b : I) : ((ν (p.γ (node b))).prod volume) (full b)=reference b := by
    dsimp only [full,reference]
    rw [Measure.prod_prod,Real.volume_Icc]
    congr 2
    field_simp
    ring
  have hFsub (b : I) : p.F (node b)⊆full b := by
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 (node b)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    intro z hz
    have hh := hF z hz
    exact ⟨hh.2.1,by simpa only [hlevel b] using hh.2.2.1⟩
  have hfullBudget : (∑ b, ENNReal.ofReal (ω (p.γ (node b)))*reference b) ≤ 1 := by
    have hh := Submission.Obl.k4_quadratic_finite_greedy_cover.full_packet_mass_le_one W ν ω
      (fun b => p.γ (node b)) (fun b => p.j (node b)) (p.T level) (fun b => p.A (node b))
      hν hω hsum
      (fun b => by
        obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 (node b)
        exact hch.2.2.2.2.2.2.1)
      (fun b => by simpa only [hlevel b] using (hp.2.2.2.2.2.2.2 (node b)).2.1)
      (fun b c hne hγ hj => hp.2.2.2.2.2.2.1 (node b) (node c)
        (fun h => hne (hinj h)) ((hlevel b).trans (hlevel c).symm) hγ hj)
    simpa only [←hfull] using hh
  have hbudget : (∑ w, ENNReal.ofReal (ω w)*((ν w).prod volume) (source w)) ≤
      (∑ b, ENNReal.ofReal (ω (p.γ (node b)))*mass b)+cost := by
    calc
      _ ≤ ∑ b, ENNReal.ofReal (ω (p.γ (node b)))*
          ((ν (p.γ (node b))).prod volume) (source (p.γ (node b))∩p.F (node b)) :=
        weighted_cover_mass_le (fun w => (ν w).prod volume) (fun w => ENNReal.ofReal (ω w))
          (fun b => p.γ (node b)) (fun b => p.F (node b)) source hcover
      _ ≤ ∑ b, ENNReal.ofReal (ω (p.γ (node b)))*(mass b+cost*reference b) :=
        Finset.sum_le_sum (fun b _ => mul_le_mul' le_rfl (hloss b))
      _ = (∑ b, ENNReal.ofReal (ω (p.γ (node b)))*mass b)+
          cost*(∑ b, ENNReal.ofReal (ω (p.γ (node b)))*reference b) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ _ := by simpa only [mul_one] using add_le_add le_rfl (mul_le_mul' le_rfl hfullBudget)
  have hretained : ENNReal.ofReal density ≤ ∑ b, ENNReal.ofReal (ω (p.γ (node b)))*mass b :=
    Submission.Obl.k4_scalar_grid_cartesian_field.pruning_mass_floor
      ENNReal.ofReal_ne_top hmass hbudget hcost
  have hfinite (b : I) : ((ν (p.γ (node b))).prod volume) (full b)≠∞ := by
    letI : IsProbabilityMeasure (ν (p.γ (node b))) := hν _
    rw [hfull]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  obtain ⟨b,hw,hpos,hfloor⟩ := exists_dense_packet_of_unit_budget
    (fun w => (ν w).prod volume) ω (fun b => p.γ (node b)) full kept hdensity hfinite
    (fun b => (hsub b).trans (fun z hz => hFsub b hz.2)) hretained
    (by simpa only [hfull] using hfullBudget)
  rw [hfull] at hpos hfloor
  exact ⟨b,hw,(mul_ne_zero_iff.mp hpos).1,hfloor⟩

end Path
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
