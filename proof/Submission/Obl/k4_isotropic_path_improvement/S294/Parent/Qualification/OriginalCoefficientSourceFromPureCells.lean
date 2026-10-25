-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalCoefficientSourceFromPureCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicCoefficientSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentOriginalFloorCaps

/-! Full original coefficient floors from actual current pure-cell
numerators and the original physical census. -/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal
noncomputable section

/-- Construct all full original coefficient-bin floors from current
pure joint-cell caps. Physical floors, line durations, ordinary base
caps and rectangle caps at arbitrary heights are derived internally. -/
theorem prepare_original_coefficient_source_of_pure_cells (dimension ε : ℝ)
    (hd : 0 ≤ dimension) (hd1 : dimension < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ p₀ : ℝ, 0 < p₀ ∧
    ∀ (n L : ℕ), 0 < L → dyadicParameterWidth n ≤ p₀ →
    ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
      (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
      (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
      (A : Set Λ) (hA : MeasurableSet A) (hEA : E⊆A×ˢ Icc (0:ℝ) 1)
      (K C Kfloor Ccount : ℝ)
      (hK : 1 ≤ K) (hC : 0 ≤ C) (hKfloor : 0 < Kfloor)
      (π : Fin L → Measure (Fin 2 → ℤ)) [∀ i, IsProbabilityMeasure (π i)]
      (hcoeff : ∀ l∈A, ∀ j, |c l j| ≤ K)
      (hCoeffBudget : 2*K ≤ (dyadicParameterWidth n)^(-η))
      (hCapBudget : originalParameterCapConstant K (4200*(12*K+3)*C) dimension ≤ (dyadicParameterWidth n)^(-η))
      (hSupportBudget : 4*(4*K+6)^3*(((12*K+2)*C)*Kfloor) ≤ (dyadicParameterWidth n)^(-η))
      (hcensus : ∀ i : Fin L,
        ((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).Finite ∧
          (((originalFineState c (dyadicParameterWidth (n+i.val))) '' E).ncard:ℝ)*
            (dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension) ≤ Ccount)
      (hpure : ∀ i : Fin L, ∀ w : ℝ,
        dyadicParameterWidth (n+i.val) ≤ w → w ≤ 1 →
        ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)),
        ((ν.prod volume).restrict E) {z |
          originalBaseCode c (dyadicParameterWidth (n+i.val)) z=b ∧
          ⌊zx (c z.1) z.2/w⌋=j ∧ vbin (dyadicParameterWidth (n+i.val)) (c z.1)∈D} ≤
            ENNReal.ofReal (C*(dyadicParameterWidth (n+i.val))^3*w^dimension)*(π i) D),
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
  obtain ⟨η,hη,p₀,hp₀,hsource⟩ := prepare_original_dyadic_coefficient_source dimension ε hd hd1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro n L hL hn Λ _ ν _ c hc E hE A hA hEA K C Kfloor Ccount
    hK hC hKfloor π _ hcoeff hCoeffBudget hCapBudget hSupportBudget hcensus hpure
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hbound : ∀ᵐ z ∂((ν.prod volume).restrict E), |zx (c z.1) z.2| ≤ 3*K :=
    (ae_restrict_mem hE).mono (fun z hz => abs_zx_le (hcoeff z.1 (hEA hz).1) (hEA hz).2)
  have hwidth1 (i : Fin L) : dyadicParameterWidth (n+i.val) ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hbase (i : Fin L) (b : Fin 3 → ℤ) :
      ((ν.prod volume).restrict E) {z | originalBaseCode c (dyadicParameterWidth (n+i.val)) z=b} ≤
        ENNReal.ofReal (((12*K+2)*C)*(dyadicParameterWidth (n+i.val))^3) := by
    have h := original_base_cap_of_pure_cells (ν.prod volume) E c (dyadicParameterWidth_pos _)
      (by positivity : 0 ≤ 3*K) hC hbound (by
        intro b j
        simpa only [div_one,Real.one_rpow,mul_one,measure_univ,mem_univ,and_true] using
          hpure i 1 (hwidth1 i) le_rfl b j univ) b
    convert h using 1 <;> congr 1 <;> ring
  have hrectangle (i : Fin L) (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ)
      (J : Fin 2 → ℤ) (hpq : dyadicParameterWidth (n+i.val) ≤ q)
      (hpw : dyadicParameterWidth (n+i.val) ≤ w) :
      (ν.prod volume) {z | z∈E ∧ z.2∈Icc t₀ (t₀+dyadicParameterWidth (n+i.val)) ∧
        (∀ j, zy (c z.1) z.2 j∈Icc (Y j) (Y j+q)) ∧ zx (c z.1) z.2∈Icc left (left+w) ∧
        vbin (dyadicParameterWidth (n+i.val)) (c z.1)=J} ≤
          ENNReal.ofReal ((4200*(12*K+3)*C)*dyadicParameterWidth (n+i.val)*q^2*w^dimension)*
            (π i) {J} := by
    have h := all_height_rectangle_caps_of_pure_cells ((ν.prod volume).restrict E)
      (originalBaseCoordinates c) (fun z => zx (c z.1) z.2)
      (fun z => vbin (dyadicParameterWidth (n+i.val)) (c z.1)) J
      (dyadicParameterWidth_pos _) le_rfl (hwidth1 i) (by positivity : 0 ≤ 3*K)
      hC hd ((π i) {J}) (measure_ne_top _ _) hbound (by
        intro w hpw hw1 b j
        change ((ν.prod volume).restrict E) {z |
          originalBaseCode c (dyadicParameterWidth (n+i.val)) z=b ∧
          ⌊zx (c z.1) z.2/w⌋=j ∧ vbin (dyadicParameterWidth (n+i.val)) (c z.1)=J} ≤ _
        simpa only [mem_singleton_iff] using hpure i w hpw hw1 b j {J})
      t₀ Y left q w hpq hpw
    rw [Measure.restrict_apply' hE] at h
    convert h using 1
    · congr 1
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq,originalBaseCoordinates,Matrix.cons_val_zero]
      constructor
      · rintro ⟨hz,ht,hy,hx,hv⟩
        refine ⟨⟨ht,?_,hx,hv⟩,hz⟩
        intro j
        fin_cases j <;> exact hy _
      · rintro ⟨⟨ht,hy,hx,hv⟩,hz⟩
        refine ⟨hz,ht,?_,hx,hv⟩
        intro j
        fin_cases j <;> exact hy _
    · congr 2
      ring
  exact hsource n L hL hn Λ ν c hc E hE A hA hEA K (4200*(12*K+3)*C) Kfloor
    ((12*K+2)*C) Ccount hK (by positivity) hKfloor (by positivity) π hcoeff
    hCoeffBudget hCapBudget hSupportBudget hcensus hbase hrectangle

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
