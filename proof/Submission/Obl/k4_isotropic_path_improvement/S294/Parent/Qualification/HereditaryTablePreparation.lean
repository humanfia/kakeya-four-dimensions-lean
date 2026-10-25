-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.HereditaryTablePreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/HereditaryTablePreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.MultiscaleCalibratedFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ShearedSupport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockCalibration

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- Construct all hereditary tables from the actual original census and
moving-band caps. The common cut uses whole finest cells; its tables
refer to a fixed preceding original event and survive all later cuts. -/
theorem simultaneous_hereditary_tables_resolved {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → P3) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d C rate Rmax : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hC : 0 ≤ C) (hrate : 0 < rate)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w →
        (occupied E (fun x j => z x j) X p w).Finite ∧
        ((occupied E (fun x j => z x j) X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hbase1 : ε*(2:ℝ)^steps ≤ 1) (hbaseθ : ε*(2:ℝ)^steps ≤ θ)
    (level : I → ℕ)
    (hwidth1 : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ 1)
    (hwidthθ : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ θ)
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, ε ≤ R → R ≤ Rmax →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | z x∈U ∧ |θ*X x-c (z x)| ≤ R} ≤
        ENNReal.ofReal (C*θ^(-d)*R^d)*reference*volume U) :
    let base := ε*(2:ℝ)^steps
    let Y := fun x => θ*X x
    let state := gridCode (fun x j => z x j) Y base base
    let point := fun x => Fin.snoc (fun j : Fin 3 => z x j) (Y x)
    ∃ U : Set ((Fin 3 → ℤ) × ℤ), MeasurableSet U ∧
      μ univ ≤ μ (state ⁻¹' U) +
        ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*((Fintype.card I:ℝ)*rate))*reference ∧
      MeasurableSet (E ∩ state ⁻¹' U) ∧
      (∀ᵐ x ∂(μ.restrict (state ⁻¹' U)), x∈E ∩ state ⁻¹' U) ∧
      (∀ x, state x∈U →
        (μ.restrict (state ⁻¹' U)) (state ⁻¹' {state x}) ≠ 0) ∧
      ∀ i : I, ∀ n : ℕ, (base*(2:ℝ)^(level i))*(2:ℝ)^n ≤ Rmax →
        ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
          (P.card:ℝ) ≤ (8*C/rate)*
            (((base*(2:ℝ)^(level i))*(2:ℝ)^n)/(base*(2:ℝ)^(level i)))^((3:ℝ)+d) ∧
          (∀ x∈E ∩ state ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (point x)=q →
              ShearedSupport.code (base*(2:ℝ)^(level i)) (point x)∈P) ∧
          ∀ a∈P, ∃ x∈E ∩ state ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (point x)=q ∧
              ShearedSupport.code (base*(2:ℝ)^(level i)) (point x)=a := by
  classical
  dsimp only
  let base := ε*(2:ℝ)^steps
  let Y := fun x => θ*X x
  let state := gridCode (fun x j => z x j) Y base base
  have hz' : Measurable (fun x j => z x j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp hz
  have hY : Measurable Y := hX.const_mul θ
  have hstate : Measurable state := ParentSource.measurable_product_gridCode _ hz' Y hY base base
  obtain ⟨U,hU,hloss,hfloor,hpositive⟩ := simultaneous_floors μ E hsupport
    (fun x j => z x j) hz' X hX hε hθ hK hθK hcensus steps hsteps hbase1 hbaseθ
    level hwidth1 hwidthθ (fun _ => rate) (fun _ => hrate.le) reference
  have hR : MeasurableSet (state ⁻¹' U) := hstate hU
  have hfull : ∀ᵐ x ∂(μ.restrict (state ⁻¹' U)), x∈E ∩ state ⁻¹' U := by
    have hEae : ∀ᵐ x ∂(μ.restrict (state ⁻¹' U)), x∈E :=
      ae_mono Measure.restrict_le_self hsupport
    filter_upwards [hEae,ae_restrict_mem hR] with x hxE hxR
    exact ⟨hxE,hxR⟩
  refine ⟨U,hU,?_,hE.inter hR,hfull,hpositive,?_⟩
  · simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hloss
  · intro i n hRmax q
    let width := base*(2:ℝ)^(level i)
    let coarse := width*(2:ℝ)^n
    have hw : 0 < width := by dsimp [width,base]; positivity
    have hc : 0 < coarse := by dsimp [coarse]; positivity
    have hfl : ∀ x∈E ∩ state ⁻¹' U,
        ENNReal.ofReal (rate*θ^(-d)*width^3*width^d)*reference ≤
          (μ.restrict (state ⁻¹' U))
            ((gridCode (fun x j => z x j) Y width width) ⁻¹'
              {gridCode (fun x j => z x j) Y width width x}) := by
      intro x hx
      have hh := hfloor i x hx.2
      change ENNReal.ofReal (rate*θ^(-d)*width^((3:ℝ)+d))*reference ≤
        (μ.restrict (state ⁻¹' U))
          ((gridCode (fun x j => z x j) Y width width) ⁻¹'
            {gridCode (fun x j => z x j) Y width width x}) at hh
      have heq : width^((3:ℝ)+d)=width^3*width^d := by
        rw [Real.rpow_add hw]
        norm_num
      rw [heq] at hh
      simpa only [mul_assoc] using hh
    have hεcoarse : ε ≤ coarse := by
      dsimp only [coarse,width,base]
      calc
        ε ≤ ε*(2:ℝ)^steps := le_mul_of_one_le_right hε.le (one_le_pow₀ (by norm_num))
        _ ≤ ε*(2:ℝ)^steps*(2:ℝ)^(level i) :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
        _ ≤ ε*(2:ℝ)^steps*(2:ℝ)^(level i)*(2:ℝ)^n :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    obtain ⟨P,hP,hcover,hwitness⟩ := HereditaryClockSupport.exists_hereditary_support
      (μ.restrict (state ⁻¹' U)) z hz Y hY (E ∩ state ⁻¹' U) reference href hreftop
      hw hw hc hθ hrate hC n n rfl rfl hfl (by
        intro V hV c hcm
        apply (show (μ.restrict (state ⁻¹' U))
          {x | z x∈V ∧ |Y x-c (z x)| ≤ coarse} ≤
            μ {x | z x∈V ∧ |Y x-c (z x)| ≤ coarse} from Measure.restrict_le_self _).trans
        exact hband coarse hεcoarse hRmax V hV c hcm) q
    refine ⟨P,hP.trans_eq ?_,?_,?_⟩
    · rw [Real.rpow_add (div_pos hc hw)]
      norm_num only [Real.rpow_ofNat]
      ring
    · intro x hx hq
      have hq' : gridCode (fun x j => z x j) Y coarse coarse x=q := by
        simpa only [ShearedSupport.code,Fin.snoc_castSucc,show (3:Fin 4)=Fin.last 3 from rfl,
          Fin.snoc_last,gridCode] using hq
      have hh := hcover x hx hq'
      simpa only [ShearedSupport.code,Fin.snoc_castSucc,show (3:Fin 4)=Fin.last 3 from rfl,
        Fin.snoc_last,gridCode] using hh
    · intro a ha
      obtain ⟨x,hx,hq,ha⟩ := hwitness a ha
      refine ⟨x,hx,?_,?_⟩
      · simpa only [ShearedSupport.code,Fin.snoc_castSucc,show (3:Fin 4)=Fin.last 3 from rfl,
          Fin.snoc_last,gridCode] using hq
      · simpa only [ShearedSupport.code,Fin.snoc_castSucc,show (3:Fin 4)=Fin.last 3 from rfl,
          Fin.snoc_last,gridCode] using ha


/-- The unrestricted-radius interface is a consequence of the resolved
one; no sub-resolution radius is used by its construction. -/
theorem simultaneous_hereditary_tables {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → P3) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d C rate Rmax : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hC : 0 ≤ C) (hrate : 0 < rate)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w →
        (occupied E (fun x j => z x j) X p w).Finite ∧
        ((occupied E (fun x j => z x j) X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hbase1 : ε*(2:ℝ)^steps ≤ 1) (hbaseθ : ε*(2:ℝ)^steps ≤ θ)
    (level : I → ℕ)
    (hwidth1 : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ 1)
    (hwidthθ : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ θ)
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, 0 < R → R ≤ Rmax →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | z x∈U ∧ |θ*X x-c (z x)| ≤ R} ≤
        ENNReal.ofReal (C*θ^(-d)*R^d)*reference*volume U) :
    let base := ε*(2:ℝ)^steps
    let Y := fun x => θ*X x
    let state := gridCode (fun x j => z x j) Y base base
    let point := fun x => Fin.snoc (fun j : Fin 3 => z x j) (Y x)
    ∃ U : Set ((Fin 3 → ℤ) × ℤ), MeasurableSet U ∧
      μ univ ≤ μ (state ⁻¹' U) +
        ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*((Fintype.card I:ℝ)*rate))*reference ∧
      MeasurableSet (E ∩ state ⁻¹' U) ∧
      (∀ᵐ x ∂(μ.restrict (state ⁻¹' U)), x∈E ∩ state ⁻¹' U) ∧
      (∀ x, state x∈U →
        (μ.restrict (state ⁻¹' U)) (state ⁻¹' {state x}) ≠ 0) ∧
      ∀ i : I, ∀ n : ℕ, (base*(2:ℝ)^(level i))*(2:ℝ)^n ≤ Rmax →
        ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
          (P.card:ℝ) ≤ (8*C/rate)*
            (((base*(2:ℝ)^(level i))*(2:ℝ)^n)/(base*(2:ℝ)^(level i)))^((3:ℝ)+d) ∧
          (∀ x∈E ∩ state ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (point x)=q →
              ShearedSupport.code (base*(2:ℝ)^(level i)) (point x)∈P) ∧
          ∀ a∈P, ∃ x∈E ∩ state ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (point x)=q ∧
              ShearedSupport.code (base*(2:ℝ)^(level i)) (point x)=a := by
  exact simultaneous_hereditary_tables_resolved μ E hE hsupport z hz X hX hε hθ hK hθK hC hrate
    hcensus steps hsteps hbase1 hbaseθ level hwidth1 hwidthθ reference href hreftop
    (fun R hεR hRmax U hU c hcm => hband R (hε.trans_le hεR) hRmax U hU c hcm)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockCalibration
