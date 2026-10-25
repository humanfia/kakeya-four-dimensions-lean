-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.SameLevelPacketCuts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal BigOperators

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Simultaneous cuts in any selected family of packets at ONE level
pay a single full original-reference charge. Exact local slices let
child-dependent states be prepared before any whole-ancestor-state cut.
No coverage hypothesis or number of packets enters the budget. -/
theorem Native.PreparedAngularPath.assemble_same_level_packet_cuts
    (selected : Set (Fin p.C)) (level : ℕ)
    (hlevel : ∀ b∈selected, p.lev b=level)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w⊆Q.base w)
    (G : Fin p.C → Set Ev) (hG : ∀ b, b∈selected → MeasurableSet (G b))
    (charge : ENNReal)
    (hcut : ∀ b, b∈selected →
      ((d.ν k (p.γ b)).prod volume) ((E (p.γ b)∩p.F b)\G b) ≤
        charge*(d.ν k (p.γ b) (p.A b)*
          ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹))) :
    ∃ keep : Fin (d.W k) → Set Ev,
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤ charge ∧
      ∀ b, b∈selected → keep (p.γ b)∩p.F b=(E (p.γ b)∩p.F b)∩G b := by
  classical
  let drop := fun w => ⋃ b : Fin p.C, if b∈selected ∧ p.γ b=w then (E w∩p.F b)\G b else ∅
  let keep := fun w => E w\drop w
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hdrop (w) : MeasurableSet (drop w) := by
    apply MeasurableSet.iUnion
    intro b
    split_ifs with hb
    · exact ((hE w).inter (hF b)).diff (hG b hb.1)
    · exact MeasurableSet.empty
  have hkeep (w) : MeasurableSet (keep w) := (hE w).diff (hdrop w)
  have hsub (w) : keep w⊆E w := sdiff_subset
  have hlocal (w) :
      ((d.ν k w).prod volume) (E w\keep w) ≤
        ∑ b : Fin p.C, ((d.ν k w).prod volume)
          (if b∈selected ∧ p.γ b=w then (E w∩p.F b)\G b else ∅) := by
    apply (measure_mono (show E w\keep w⊆drop w from fun z hz => by
      by_contra hh
      exact hz.2 ⟨hz.1,hh⟩)).trans
    exact measure_iUnion_fintype_le _ _
  have hsingle (b : Fin p.C) :
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume)
        (if b∈selected ∧ p.γ b=w then (E w∩p.F b)\G b else ∅))=
      if b∈selected then ENNReal.ofReal (d.ω k (p.γ b))*
        ((d.ν k (p.γ b)).prod volume) ((E (p.γ b)∩p.F b)\G b) else 0 := by
    by_cases hb : b∈selected
    · simp only [hb,true_and,if_pos]
      simp only [apply_ite,measure_empty,mul_ite,mul_zero]
      simp
    · simp only [hb,false_and,ite_false,measure_empty,mul_zero,Finset.sum_const_zero]
  have hbudget :
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤ charge := by
    calc
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
          ∑ b : Fin p.C, ((d.ν k w).prod volume)
            (if b∈selected ∧ p.γ b=w then (E w∩p.F b)\G b else ∅) :=
        Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (hlocal w))
      _ = ∑ b : Fin p.C, if b∈selected then ENNReal.ofReal (d.ω k (p.γ b))*
          ((d.ν k (p.γ b)).prod volume) ((E (p.γ b)∩p.F b)\G b) else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun b _ => hsingle b)
      _ ≤ ∑ b : Fin p.C, charge*(if b∈selected then ENNReal.ofReal (d.ω k (p.γ b))*
          (d.ν k (p.γ b) (p.A b)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) else 0) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : b∈selected
        · simp only [if_pos hb]
          exact (mul_le_mul' le_rfl (hcut b hb)).trans_eq (by ac_rfl)
        · simp only [if_neg hb,mul_zero,le_refl]
      _ = charge*(∑ b : Fin p.C, if b∈selected then ENNReal.ofReal (d.ω k (p.γ b))*
          (d.ν k (p.γ b) (p.A b)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) else 0) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ charge*1 := by
        apply mul_le_mul' le_rfl
        have h := hp.full_reference_mass_le_one (hd.weights k).2.2 (hd.weights k).1
          (hd.weights k).2.1 level
        apply le_trans (Finset.sum_le_sum (fun b _ => ?_)) h
        by_cases hb : b∈selected
        · have hl : p.lev b=level := hlevel b hb
          simp only [if_pos hb,hl,ite_true]
          exact le_of_eq (by ac_rfl)
        · simp only [if_neg hb]
          exact zero_le
      _ = charge := mul_one _
  refine ⟨keep,(fun w => ⟨hkeep w,hsub w⟩),hbudget,?_⟩
  intro b hb
  ext z
  constructor
  · rintro ⟨⟨hzE,hzkeep⟩,hzF⟩
    refine ⟨⟨hzE,hzF⟩,?_⟩
    by_contra hzG
    exact hzkeep (mem_iUnion.mpr ⟨b,by simpa only [hb,and_true,eq_self,ite_true] using
      (show z∈(E (p.γ b)∩p.F b)\G b from ⟨⟨hzE,hzF⟩,hzG⟩)⟩)
  · rintro ⟨⟨hzE,hzF⟩,hzG⟩
    refine ⟨⟨hzE,?_⟩,hzF⟩
    intro hzdrop
    obtain ⟨b',hb'⟩ := mem_iUnion.mp hzdrop
    by_cases hactive : b'∈selected ∧ p.γ b'=p.γ b
    · rw [if_pos hactive] at hb'
      have heq : b'=b := Q.base_packet_unique (p.γ b) z (hbase _ hzE) b' b
        ((hlevel b' hactive.1).trans (hlevel b hb).symm) hactive.2 rfl hb'.1.2 hzF
      subst b'
      exact hb'.2 hzG
    · simpa only [if_neg hactive,mem_empty_iff_false] using hb'

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
