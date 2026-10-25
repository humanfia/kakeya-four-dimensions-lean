-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalDyadicCoefficientSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicOriginalPhysicalFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalLineDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicParameterFloors

/-! The physical census and actual current caps construct the full
ORIGINAL coefficient-bin floors. No reference-floor or occupation-floor
certificate is supplied. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Construct one coefficient-floor source on all tested dyadic scales.
First restore physical floors by whole finest cells, then remove short
original lines, then invoke the original-prior scalar cleanup. Its
multiscale cleanup cost is geometric, independent of the number of scales. -/
theorem prepare_original_dyadic_coefficient_source (dimension ε : ℝ)
    (hd : 0 ≤ dimension) (hd1 : dimension < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ p₀ : ℝ, 0 < p₀ ∧
    ∀ (n L : ℕ), 0 < L → dyadicParameterWidth n ≤ p₀ →
    ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
      (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
      (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
      (A : Set Λ) (hA : MeasurableSet A) (hEA : E⊆A×ˢ Icc (0:ℝ) 1)
      (K Kr Kfloor Kbase Ccount : ℝ)
      (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hKfloor : 0 < Kfloor) (hKbase : 0 ≤ Kbase)
      (π : Fin L → Measure (Fin 2 → ℤ)) [∀ i, IsProbabilityMeasure (π i)]
      (hcoeff : ∀ l∈A, ∀ j, |c l j| ≤ K)
      (hCoeffBudget : 2*K ≤ (dyadicParameterWidth n)^(-η))
      (hCapBudget : originalParameterCapConstant K Kr dimension ≤ (dyadicParameterWidth n)^(-η))
      (hSupportBudget : 4*(4*K+6)^3*(Kbase*Kfloor) ≤ (dyadicParameterWidth n)^(-η))
      (hcensus : ∀ i : Fin L,
        ((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).Finite ∧
          (((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).ncard:ℝ)*
            (dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension) ≤ Ccount)
      (hBaseCap : ∀ i : Fin L, ∀ q,
        ((ν.prod volume).restrict E)
          {z | originalBaseCode c (dyadicParameterWidth (n+i.val)) z=q} ≤
            ENNReal.ofReal (Kbase*(dyadicParameterWidth (n+i.val))^3))
      (hrect : ∀ i : Fin L, ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ) (J : Fin 2 → ℤ),
        dyadicParameterWidth (n+i.val) ≤ q → dyadicParameterWidth (n+i.val) ≤ w →
        (ν.prod volume) {z | z∈E ∧ z.2∈Icc t₀ (t₀+dyadicParameterWidth (n+i.val)) ∧
          (∀ j, zy (c z.1) z.2 j∈Icc (Y j) (Y j+q)) ∧ zx (c z.1) z.2∈Icc left (left+w) ∧
          vbin (dyadicParameterWidth (n+i.val)) (c z.1)=J} ≤
            ENNReal.ofReal (Kr*dyadicParameterWidth (n+i.val)*q^2*w^dimension)*(π i) {J}),
      ∃ (Ephys R : Set (Λ × ℝ)), MeasurableSet Ephys ∧ MeasurableSet R ∧ R⊆Ephys ∧ Ephys⊆E ∧
        (ν.prod volume) (E\R) ≤ ENNReal.ofReal (Ccount*(L:ℝ)/Kfloor)+
          ENNReal.ofReal K⁻¹+
          ENNReal.ofReal (((4*K+2)^2)*(dyadicParameterWidth n)^η/(1-(2:ℝ)^(-η))) ∧
        (∀ i : Fin L, ∀ z∈Ephys,
          ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension)/Kfloor) ≤
            ((ν.prod volume).restrict Ephys)
              ((originalFineState c (dyadicParameterWidth (n+i.val))) ⁻¹'
                {originalFineState c (dyadicParameterWidth (n+i.val)) z})) ∧
        ∀ i : Fin L, ∀ z∈R,
          ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^(2+dimension)*
            (dyadicParameterWidth (n+i.val))^ε)*(π i)
              {vbin (dyadicParameterWidth (n+i.val)) (c z.1)} ≤
            ν {l | parameterCode (dyadicParameterWidth (n+i.val)) (c l)=
              parameterCode (dyadicParameterWidth (n+i.val)) (c z.1)} := by
  obtain ⟨η,hη,p₀,hp₀,hcleanup⟩ := original_dyadic_parameter_floors
    dimension ε hd hd1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro n L hL hn Λ _ ν _ c hc E hE A hA hEA K Kr Kfloor Kbase Ccount
    hK hKr hKfloor hKbase π _ hcoeff hCoeffBudget hCapBudget hSupportBudget hcensus hBaseCap hrect
  let raw := ν.prod (volume : Measure ℝ)
  let μ := raw.restrict E
  have hunit : E⊆univ×ˢ Icc (0:ℝ) 1 := fun z hz => ⟨mem_univ _,(hEA hz).2⟩
  haveI : IsFiniteMeasure μ := (original_unit_event_time_kernel ν hE hunit).1
  obtain ⟨U,Ephys,hU,_hEphysDef,hEphys,hEphysE,hlossPhys,hphysical,_hpositive⟩ :=
    prepare_original_dyadic_physical_floors μ c hc E hE (ae_restrict_mem hE)
      n L hL dimension Ccount Kfloor hKfloor hcensus
  let reference := raw.restrict Ephys
  have hrefEq : μ.restrict Ephys=reference := by
    dsimp only [μ,reference]
    exact Measure.restrict_restrict_of_subset hEphysE
  haveI : IsFiniteMeasure reference := by rw [←hrefEq]; infer_instance
  have hphysical' (i : Fin L) (z : Λ × ℝ) (hz : z∈Ephys) :
      ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension)/Kfloor) ≤
        reference ((originalFineState c (dyadicParameterWidth (n+i.val))) ⁻¹'
          {originalFineState c (dyadicParameterWidth (n+i.val)) z}) := by
    rw [←hrefEq]
    exact hphysical i z hz
  have hmassEphys : μ Ephys=raw Ephys :=
    Measure.restrict_eq_self (μ:=raw) hEphysE
  have hphysLoss : raw (E\Ephys) ≤ ENNReal.ofReal (Ccount*(L:ℝ)/Kfloor) := by
    have hfin : raw Ephys≠∞ := hmassEphys ▸ measure_ne_top μ Ephys
    apply (measure_sdiff_le_iff_le_add hEphys.nullMeasurableSet hEphysE hfin).2
    simpa only [μ,Measure.restrict_apply_univ,hmassEphys] using hlossPhys
  obtain ⟨S,hS,hSA,hlossDuration,hlong⟩ := exists_original_line_duration_source ν
    Ephys hEphys A hA (fun z hz => ⟨(hEA (hEphysE hz)).1,mem_univ _⟩) (ENNReal.ofReal K⁻¹)
  let middle := Ephys∩(S×ˢ univ)
  have hmiddle : MeasurableSet middle := hEphys.inter (hS.prod MeasurableSet.univ)
  have hmiddleEphys : middle⊆Ephys := inter_subset_left
  have hmiddleE : middle⊆E := hmiddleEphys.trans hEphysE
  have hmiddleS : middle⊆S×ˢ Icc (0:ℝ) 1 :=
    fun z hz => ⟨hz.2.1,(hEA (hmiddleE hz)).2⟩
  have hbase (i : Fin L) (q) :
      reference {z | originalBaseCode c (dyadicParameterWidth (n+i.val)) z=q} ≤
        ENNReal.ofReal (Kbase*(dyadicParameterWidth (n+i.val))^3) :=
    (Measure.restrict_mono hEphysE le_rfl _).trans (hBaseCap i q)
  have hrectangle (i : Fin L) (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ) (J : Fin 2 → ℤ)
      (hq : dyadicParameterWidth (n+i.val) ≤ q) (hw : dyadicParameterWidth (n+i.val) ≤ w) :
      raw {z | z∈middle ∧ z.2∈Icc t₀ (t₀+dyadicParameterWidth (n+i.val)) ∧
        (∀ j, zy (c z.1) z.2 j∈Icc (Y j) (Y j+q)) ∧ zx (c z.1) z.2∈Icc left (left+w) ∧
        vbin (dyadicParameterWidth (n+i.val)) (c z.1)=J} ≤
          ENNReal.ofReal (Kr*dyadicParameterWidth (n+i.val)*q^2*w^dimension)*(π i) {J} := by
    apply le_trans ?_ (hrect i t₀ Y left q w J hq hw)
    apply measure_mono
    intro z hz
    exact ⟨hmiddleE hz.1,hz.2⟩
  obtain ⟨lines,hlines,hlinesS,hlossCleanup,hfloors⟩ := hcleanup n L hn Λ ν reference c hc
    middle hmiddle S hS hmiddleS K Kr Kfloor Kbase hK hKr hKfloor hKbase π
    (fun l hl => hcoeff l (hSA hl)) hlong hCoeffBudget hCapBudget hSupportBudget
    (fun i z hz => hphysical' i z hz.1) hbase hrectangle
  let R := middle∩(lines×ˢ univ)
  have hR : MeasurableSet R := hmiddle.inter (hlines.prod MeasurableSet.univ)
  have hRm : R⊆middle := inter_subset_left
  have hcleanupSet : middle\R=middle∩((S\lines)×ˢ univ) := by
    ext z
    simp only [R,middle,mem_sdiff,mem_inter_iff,mem_prod,mem_univ,and_true]
    tauto
  have hcover : E\R ⊆ (E\Ephys)∪((Ephys\middle)∪(middle\R)) := by
    intro z hz
    by_cases h0 : z∈Ephys
    · by_cases h1 : z∈middle
      · exact Or.inr (Or.inr ⟨h1,hz.2⟩)
      · exact Or.inr (Or.inl ⟨h0,h1⟩)
    · exact Or.inl ⟨hz.1,h0⟩
  refine ⟨Ephys,R,hEphys,hR,hRm.trans hmiddleEphys,hEphysE,?_,hphysical',?_⟩
  · calc
      raw (E\R) ≤ raw ((E\Ephys)∪((Ephys\middle)∪(middle\R))) := measure_mono hcover
      _ ≤ raw (E\Ephys)+(raw (Ephys\middle)+raw (middle\R)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ _ := by
        rw [hcleanupSet]
        have hDuration : raw (Ephys\middle) ≤ ENNReal.ofReal K⁻¹ := by
          simpa only [measure_univ,mul_one] using hlossDuration
        have h := add_le_add hphysLoss (add_le_add hDuration hlossCleanup)
        simpa only [add_assoc] using h
  · intro i z hz
    exact hfloors i z.1 hz.2.1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
