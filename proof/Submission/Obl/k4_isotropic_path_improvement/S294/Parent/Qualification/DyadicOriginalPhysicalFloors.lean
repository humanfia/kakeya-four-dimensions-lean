-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicOriginalPhysicalFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WholeStateFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Literal original physical codes coarsen on the original dyadic grid. -/
theorem coarsen_originalFineState {Λ : Type*} (c : Λ → Fin 7 → ℝ)
    {i j : ℕ} (hij : i ≤ j) (z : Λ × ℝ) :
    coarsenParameterCode (j-i) (originalFineState c (dyadicParameterWidth j) z) =
      originalFineState c (dyadicParameterWidth i) z := by
  change coarsenParameterCode (j-i) (parameterCode (dyadicParameterWidth j) (zpos (c z.1) z.2)) =
    parameterCode (dyadicParameterWidth i) (zpos (c z.1) z.2)
  simpa only [one_mul] using
    coarsen_nested_parameterCode 1 (by norm_num) hij (zpos (c z.1) z.2)

/-- One union of whole finest physical states restores the floors at
every queried dyadic width. The input is the actual occupied-cell census;
the original current law and all surviving finest conditional laws stay fixed. -/
theorem prepare_original_dyadic_physical_floors {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (hfull : ∀ᵐ z ∂μ, z∈E)
    (n L : ℕ) (hL : 0 < L) (dimension C Kfloor : ℝ) (hKfloor : 0 < Kfloor)
    (hcensus : ∀ i : Fin L,
      ((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).Finite ∧
        (((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).ncard:ℝ)*
          (dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension) ≤ C) :
    ∃ (U : Set (Fin 4 → ℤ)) (R : Set (Λ × ℝ)),
      MeasurableSet U ∧ R=E∩(originalFineState c (dyadicParameterWidth (n+L-1))) ⁻¹' U ∧
      MeasurableSet R ∧ R⊆E ∧
      μ univ ≤ μ R+ENNReal.ofReal (C*(L:ℝ)/Kfloor) ∧
      (∀ i : Fin L, ∀ z∈R,
        ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension)/Kfloor) ≤
          (μ.restrict R) ((originalFineState c (dyadicParameterWidth (n+i.val))) ⁻¹'
            {originalFineState c (dyadicParameterWidth (n+i.val)) z})) ∧
      ∀ z∈R, (μ.restrict R)
        ((originalFineState c (dyadicParameterWidth (n+L-1))) ⁻¹'
          {originalFineState c (dyadicParameterWidth (n+L-1)) z}) ≠ 0 := by
  classical
  let last : Fin L := ⟨L-1,by omega⟩
  let state := originalFineState c (dyadicParameterWidth (n+L-1))
  let F := (hcensus last).1.toFinset
  let code (i : Fin L) := coarsenParameterCode ((n+L-1)-(n+i.val)) (m:=4)
  let cost (i : Fin L) := ENNReal.ofReal
    ((dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension)/Kfloor)
  have hm : Measurable state := measurable_originalFineState hc _
  have hfactor (i : Fin L) (z : Λ × ℝ) :
      code i (state z)=originalFineState c (dyadicParameterWidth (n+i.val)) z :=
    coarsen_originalFineState c (by omega) z
  have hcarrier : ∀ᵐ z ∂μ, state z∈F := hfull.mono (by
    intro z hz
    apply (hcensus last).1.mem_toFinset.mpr
    refine ⟨z,hz,?_⟩
    dsimp only [state,last]
    congr 2 <;> omega)
  have hbudget (i : Fin L) : ∑ _a∈F.image (code i), cost i ≤ ENNReal.ofReal (C/Kfloor) := by
    have hsub : (↑(F.image (code i)) : Set (Fin 4 → ℤ)) ⊆
        (originalFineState c (dyadicParameterWidth (n+i.val))) '' E := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨z,hz,hqz⟩ := (hcensus last).1.mem_toFinset.mp hq
      have hs : state z=q := by
        convert hqz using 1 <;> dsimp only [last,state] <;> congr 2 <;> omega
      exact ⟨z,hz,(hfactor i z).symm.trans (congrArg (code i) hs)⟩
    have hcard : ((F.image (code i)).card:ℝ) ≤
        (((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).ncard:ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub (hcensus i).1
    simp only [Finset.sum_const,nsmul_eq_mul,cost]
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (((F.image (code i)).card:ℝ)*
        (dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension))/Kfloor := by ring
      _ ≤ C/Kfloor := div_le_div_of_nonneg_right
        ((mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (dyadicParameterWidth_pos _).le _)).trans
          (hcensus i).2) hKfloor.le
  obtain ⟨U,hU,_hUF,hloss,hfloor,hpositive⟩ := simultaneous_whole_state_floors
    μ state hm F hcarrier code (fun i _ => cost i)
  let keep := state ⁻¹' U
  let R := E∩keep
  have hkeep : MeasurableSet keep := hm hU
  have hR : MeasurableSet R := hE.inter hkeep
  have hrestrict : μ.restrict R=μ.restrict keep := by
    apply Measure.restrict_congr_set
    filter_upwards [hfull] with z hz
    simp only [R,mem_inter_iff,hz,true_and]
  have hmeasure : μ R=μ keep := by
    have h := congrArg (fun ξ : Measure (Λ×ℝ) => ξ univ) hrestrict
    simpa only [Measure.restrict_apply_univ] using h
  refine ⟨U,R,hU,rfl,hR,inter_subset_left,?_,?_,?_⟩
  · rw [hmeasure]
    apply hloss.trans
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ _i : Fin L, ENNReal.ofReal (C/Kfloor) :=
        Finset.sum_le_sum (fun i _ => hbudget i)
      _ = ENNReal.ofReal (C*(L:ℝ)/Kfloor) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg L)]
        congr 1
        ring
  · intro i z hz
    have h := hfloor i z hz.2
    rw [←hrestrict] at h
    simpa only [←hfactor i,cost,Set.preimage,Set.mem_singleton_iff] using h
  · intro z hz
    rw [hrestrict]
    exact hpositive z hz.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
