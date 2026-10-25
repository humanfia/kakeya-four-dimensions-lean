-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.HereditaryTables, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/HereditaryTables.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.HereditaryTablePreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripCensusGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- Literal first three coordinates of the original physical point. -/
def originalBase (p : PhysicalModel) (x : Ev) : P3 :=
  WithLp.toLp 2 (fun j : Fin 3 => p.originalPoint x j.castSucc)

theorem measurable_originalPoint (p : PhysicalModel) : Measurable p.originalPoint :=
  p.measurable_physical_coordinates

theorem measurable_originalBase (p : PhysicalModel) : Measurable p.originalBase := by
  apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_pi_apply j.castSucc).comp p.measurable_originalPoint

/-- A single original whole-state cut constructs all physical hereditary
tables used by scalar filling. The input height is the original signal
divided by its exact height/clock ratio; no new reference law is chosen. -/
theorem original_hereditary_table_preparation_resolved {I : Type*} [Fintype I]
    (p : PhysicalModel) (μ : Measure Ev) [IsFiniteMeasure μ]
    (E : Set Ev) (hE : MeasurableSet E) (hsupport : ∀ᵐ x ∂μ, x∈E)
    {ε θ K d C rate Rmax : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hC : 0 ≤ C) (hrate : 0 < rate)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ θ*w →
        (occupied E (fun x j => p.originalBase x j) (fun x => p.originalPoint x 3/θ) b w).Finite ∧
        ((occupied E (fun x j => p.originalBase x j)
          (fun x => p.originalPoint x 3/θ) b w).ncard:ℝ) ≤ K/(b^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hbase1 : ε*(2:ℝ)^steps ≤ 1) (hbaseθ : ε*(2:ℝ)^steps ≤ θ)
    (level : I → ℕ)
    (hwidth1 : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ 1)
    (hwidthθ : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ θ)
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, ε ≤ R → R ≤ Rmax →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | p.originalBase x∈U ∧ |p.originalPoint x 3-c (p.originalBase x)| ≤ R} ≤
        ENNReal.ofReal (C*θ^(-d)*R^d)*reference*volume U) :
    let base := ε*(2:ℝ)^steps
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ μ ((p.physicalState base) ⁻¹' U) +
        ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*((Fintype.card I:ℝ)*rate))*reference ∧
      MeasurableSet (E ∩ (p.physicalState base) ⁻¹' U) ∧
      (∀ᵐ x ∂(μ.restrict ((p.physicalState base) ⁻¹' U)),
        x∈E ∩ (p.physicalState base) ⁻¹' U) ∧
      (∀ x, p.physicalState base x∈U →
        (μ.restrict ((p.physicalState base) ⁻¹' U))
          ((p.physicalState base) ⁻¹' {p.physicalState base x}) ≠ 0) ∧
      ∀ i : I, ∀ n : ℕ, (base*(2:ℝ)^(level i))*(2:ℝ)^n ≤ Rmax →
        ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
          (P.card:ℝ) ≤ (8*C/rate)*
            (((base*(2:ℝ)^(level i))*(2:ℝ)^n)/(base*(2:ℝ)^(level i)))^((3:ℝ)+d) ∧
          ∀ x∈E ∩ (p.physicalState base) ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (p.originalPoint x)=q →
              ShearedSupport.code (base*(2:ℝ)^(level i)) (p.originalPoint x)∈P := by
  classical
  dsimp only
  let base := ε*(2:ℝ)^steps
  let X := fun x => p.originalPoint x 3/θ
  let Y := fun x => θ*X x
  have hY (x : Ev) : Y x=p.originalPoint x 3 := by
    dsimp only [Y,X]
    field_simp
  have hX : Measurable X :=
    ((measurable_pi_apply 3).comp p.measurable_originalPoint).div_const θ
  obtain ⟨U,hU,hloss,hEref,hfull,hpositive,htables⟩ :=
    ClockCalibration.simultaneous_hereditary_tables_resolved μ E hE hsupport p.originalBase
      p.measurable_originalBase X hX hε hθ hK hθK hC hrate hcensus steps hsteps
      hbase1 hbaseθ level hwidth1 hwidthθ reference href hreftop (by
        intro R hR hRmax V hV c hcm
        change μ {x | p.originalBase x∈V ∧ |Y x-c (p.originalBase x)| ≤ R} ≤ _
        simpa only [hY] using hband R hR hRmax V hV c hcm)
  let unpack := fun q : Fin 4 → ℤ => ((fun j : Fin 3 => q j.castSucc),q 3)
  let U4 := unpack ⁻¹' U
  let state := gridCode (fun x j => p.originalBase x j) Y base base
  have hstate (x : Ev) : state x=unpack (p.physicalState base x) := by
    dsimp only [state,gridCode,unpack,originalBase,physicalState,originalPoint]
    rw [hY]
    rfl
  have hpre : state ⁻¹' U=(p.physicalState base) ⁻¹' U4 := by
    ext x
    change state x∈U ↔ unpack (p.physicalState base x)∈U
    rw [hstate]
  have hpoint (x : Ev) :
      Fin.snoc (fun j : Fin 3 => p.originalBase x j) (Y x)=p.originalPoint x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      change Y x=p.originalPoint x 3
      exact hY x
    · simp only [Fin.snoc_castSucc,originalBase,PiLp.toLp_apply]
  have hU4 : MeasurableSet U4 := (Set.to_countable _).measurableSet
  change μ univ ≤ μ (state ⁻¹' U)+_ at hloss
  change MeasurableSet (E ∩ state ⁻¹' U) at hEref
  change ∀ᵐ x ∂(μ.restrict (state ⁻¹' U)), x∈E ∩ state ⁻¹' U at hfull
  rw [hpre] at hloss hEref hfull
  refine ⟨U4,hU4,hloss,hEref,hfull,?_,?_⟩
  · intro x hx
    have hxU : state x∈U := by rw [hstate]; exact hx
    have hpos := hpositive x hxU
    have hfiber : state ⁻¹' {state x}=(p.physicalState base) ⁻¹' {p.physicalState base x} := by
      ext y
      simp only [mem_preimage,mem_singleton_iff,hstate]
      constructor
      · intro heq
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · exact congrArg Prod.snd heq
        · exact congrFun (congrArg Prod.fst heq) i
      · exact congrArg unpack
    change (μ.restrict (state ⁻¹' U)) (state ⁻¹' {state x}) ≠ 0 at hpos
    rwa [hpre,hfiber] at hpos
  · intro i n hRmax q
    obtain ⟨P,hP,hcover,-⟩ := htables i n hRmax q
    refine ⟨P,hP,?_⟩
    intro x hx hq
    have hx' : x∈E ∩ state ⁻¹' U := by simpa only [hpre] using hx
    have hh := hcover x hx'
    change ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n)
        (Fin.snoc (fun j : Fin 3 => p.originalBase x j) (Y x))=q →
      ShearedSupport.code (base*(2:ℝ)^(level i))
        (Fin.snoc (fun j : Fin 3 => p.originalBase x j) (Y x))∈P at hh
    rw [hpoint] at hh
    exact hh hq


/-- The original interface follows from the resolved-band construction. -/
theorem original_hereditary_table_preparation {I : Type*} [Fintype I]
    (p : PhysicalModel) (μ : Measure Ev) [IsFiniteMeasure μ]
    (E : Set Ev) (hE : MeasurableSet E) (hsupport : ∀ᵐ x ∂μ, x∈E)
    {ε θ K d C rate Rmax : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hC : 0 ≤ C) (hrate : 0 < rate)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ θ*w →
        (occupied E (fun x j => p.originalBase x j) (fun x => p.originalPoint x 3/θ) b w).Finite ∧
        ((occupied E (fun x j => p.originalBase x j)
          (fun x => p.originalPoint x 3/θ) b w).ncard:ℝ) ≤ K/(b^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hbase1 : ε*(2:ℝ)^steps ≤ 1) (hbaseθ : ε*(2:ℝ)^steps ≤ θ)
    (level : I → ℕ)
    (hwidth1 : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ 1)
    (hwidthθ : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ θ)
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, 0 < R → R ≤ Rmax →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | p.originalBase x∈U ∧ |p.originalPoint x 3-c (p.originalBase x)| ≤ R} ≤
        ENNReal.ofReal (C*θ^(-d)*R^d)*reference*volume U) :
    let base := ε*(2:ℝ)^steps
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ μ ((p.physicalState base) ⁻¹' U) +
        ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*((Fintype.card I:ℝ)*rate))*reference ∧
      MeasurableSet (E ∩ (p.physicalState base) ⁻¹' U) ∧
      (∀ᵐ x ∂(μ.restrict ((p.physicalState base) ⁻¹' U)),
        x∈E ∩ (p.physicalState base) ⁻¹' U) ∧
      (∀ x, p.physicalState base x∈U →
        (μ.restrict ((p.physicalState base) ⁻¹' U))
          ((p.physicalState base) ⁻¹' {p.physicalState base x}) ≠ 0) ∧
      ∀ i : I, ∀ n : ℕ, (base*(2:ℝ)^(level i))*(2:ℝ)^n ≤ Rmax →
        ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
          (P.card:ℝ) ≤ (8*C/rate)*
            (((base*(2:ℝ)^(level i))*(2:ℝ)^n)/(base*(2:ℝ)^(level i)))^((3:ℝ)+d) ∧
          ∀ x∈E ∩ (p.physicalState base) ⁻¹' U,
            ShearedSupport.code ((base*(2:ℝ)^(level i))*(2:ℝ)^n) (p.originalPoint x)=q →
              ShearedSupport.code (base*(2:ℝ)^(level i)) (p.originalPoint x)∈P := by
  exact p.original_hereditary_table_preparation_resolved μ E hE hsupport hε hθ hK hθK hC hrate
    hcensus steps hsteps hbase1 hbaseθ level hwidth1 hwidthθ reference href hreftop
    (fun R hεR hRmax U hU c hcm => hband R (hε.trans_le hεR) hRmax U hU c hcm)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
