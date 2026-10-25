-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentVelocitySpatialCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CurrentVelocitySpatialCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentEntrySpatialCaps

/-! # Original spatial preparation from discrete velocity-bin caps

Only singleton caps of one unchanged external velocity reference are
used. Summation gives every coarser velocity event; original coefficient
selectors only restrict these events further.
-/
set_option autoImplicit false
namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped ENNReal
noncomputable section

/-- Singleton caps for a countable code imply every coarser code cap. -/
theorem palette_cap_of_code_coarsening {Ω V Q J : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (π : Measure V) (code : Ω → Q) (hcode : Measurable code)
    (external : V → Q) (hext : Measurable external) (coarsen : Q → J)
    (C : ℝ≥0∞) (hcap : ∀ β, μ (code ⁻¹' {β}) ≤ C*π (external ⁻¹' {β}))
    (j : J) : μ {z | coarsen (code z)=j} ≤ C*π {v | coarsen (external v)=j} := by
  let D := coarsen ⁻¹' {j}
  calc
    _ = ∑' β : D, μ (code ⁻¹' {(β : Q)}) := by
      exact (tsum_measure_preimage_singleton (to_countable D)
        (fun β _ => hcode (measurableSet_singleton β))).symm
    _ ≤ ∑' β : D, C*π (external ⁻¹' {(β : Q)}) :=
      ENNReal.tsum_le_tsum (fun β => hcap β)
    _ = C*∑' β : D, π (external ⁻¹' {(β : Q)}) := ENNReal.tsum_mul_left
    _ = _ := by
      congr 1
      exact tsum_measure_preimage_singleton (to_countable D)
        (fun β _ => hext (measurableSet_singleton β))

namespace Jets2

def parameterVelocityHeader (β : Fin 7 → ℤ) : Fin 2 → ℤ := ![β 4,β 6]

theorem parameterVelocityHeader_code (width : ℝ) (c : Fin 7 → ℝ) :
    parameterVelocityHeader (parameterCode width c)=parameterCode width (zv c) := by
  funext i
  fin_cases i <;> rfl

/-- Current singleton velocity caps imply both current coefficient
selector families used by original spatial preparation. -/
theorem current_spatial_cap_inputs_of_velocity_bins {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (ρ ζ : ℝ) (hρ : 0 < ρ) (hζ : 0 < ζ)
    (π : Measure (Fin 2 → ℝ)) (C amplitude dimension : ℝ)
    (hcap : ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell β,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=β} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v=β}) :
    (∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
        π {v | parameterCode ρ v=parameterVelocityHeader world}) ∧
    (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ q : ℝ, ζ ≤ q → q ≤ r → ∀ world fine cell,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧ zoomParameterPiece ρ c r z.1=fine ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=parameterVelocityHeader fine}) := by
  have hcoarsened (q : ℝ) (hq : ζ ≤ q) (hq1 : q ≤ 1) (n : ℕ)
      (hn : n ≤ parameterLevel q) (world : Fin 7 → ℤ) (cell : Fin 4 → ℤ) (β : Fin 2 → ℤ) :
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth n) (zv (c z.1))=β} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth n) v=β} := by
    let U := {z : Λ×ℝ | parameterCode ρ (c z.1)=world ∧
      canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell}
    have hU : MeasurableSet U :=
      (((measurable_parameterCode ρ).comp (hc.comp measurable_fst))
        (measurableSet_singleton world)).inter
        ((measurable_canonicalZoomCell hc ρ _) (measurableSet_singleton cell))
    let velCode := fun z : Λ×ℝ =>
      parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))
    have hm : Measurable velCode := by
      apply (measurable_parameterCode _).comp
      unfold zv
      fun_prop
    have hsingle (b : Fin 2 → ℤ) :
        ((μ.restrict E).restrict U) (velCode ⁻¹' {b}) ≤
        ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
          (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
          π ((parameterCode (ρ*dyadicParameterWidth (parameterLevel q))) ⁻¹' {b}) := by
      rw [Measure.restrict_apply' hU]
      convert hcap q hq hq1 world cell b using 2
      · ext z
        simp only [U,velCode,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
        tauto
      · rfl
    have h := palette_cap_of_code_coarsening ((μ.restrict E).restrict U) π velCode hm
      (parameterCode (ρ*dyadicParameterWidth (parameterLevel q))) (measurable_parameterCode _)
      (coarsenParameterCode (parameterLevel q-n)) _ hsingle β
    dsimp only [velCode] at h
    simp only [coarsen_nested_parameterCode ρ hρ hn] at h
    rw [Measure.restrict_apply' hU] at h
    convert h using 2
    ext z
    simp only [U,mem_inter_iff,mem_ofPred_eq]
    tauto
  constructor
  · intro q hq hq1 world cell
    have h := hcoarsened q hq hq1 0 (Nat.zero_le _) world cell (parameterVelocityHeader world)
    simp only [show dyadicParameterWidth 0=1 by norm_num [dyadicParameterWidth],mul_one] at h
    refine (measure_mono ?_).trans h
    rintro z ⟨hw,hc'⟩
    refine ⟨hw,hc',?_⟩
    rw [←parameterVelocityHeader_code,hw]
  · intro r hr hr1 q hq hqr world fine cell
    have hn := parameterLevel_antitone_on_unit (hζ.trans_le hq) hqr hr1
    refine (measure_mono ?_).trans
      (hcoarsened q hq (hqr.trans hr1) (parameterLevel r) hn world cell (parameterVelocityHeader fine))
    rintro z ⟨hw,hf,hcell⟩
    refine ⟨hw,hcell,?_⟩
    have h := congrArg parameterVelocityHeader hf
    simpa only [zoomParameterPiece,parameterVelocityHeader_code] using h


/-- One unchanged reference, queried only on velocity-bin singletons,
supplies the full original spatial cap preparation. No arbitrary Borel
velocity domination or coefficient-selector cap is assumed. -/
theorem prepare_original_spatial_cap_source_of_velocity_bins
    {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ×ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    {ρ ζ cut C amplitude dimension : ℝ}
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hcut : 0 < cut)
    (hC : 0 ≤ C) (hamp : 0 ≤ amplitude) (hdim : 0 ≤ dimension)
    (hfinite : ∀ n : ℕ, n ≤ parameterLevel ζ →
      ((fun z : Λ×ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite)
    (π : Measure (Fin 2 → ℝ))
    (hcap : ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell β,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=β} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v=β}) :
    ∃ R : Set (Λ×ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ ((parameterLevel ζ+1:ℕ):ℝ≥0∞)*
        ENNReal.ofReal (cut*zoomBlockVisitConstant)*ν univ ∧
      (∀ world (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ), ζ ≤ q → q ≤ 1 →
        ν {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
          ENNReal.ofReal ((625*C/cut)*(ρ*q)^((2:ℝ)+dimension)*amplitude)*
            π {v | parameterCode ρ v=parameterVelocityHeader world}) ∧
      (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ world fine (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ),
        ζ ≤ q → q ≤ r →
        ν {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
          ENNReal.ofReal ((625*C/cut)*(ρ*q)^((2:ℝ)+dimension)*amplitude)*
            π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=parameterVelocityHeader fine}) := by
  obtain ⟨hcoarse,hfine⟩ := current_spatial_cap_inputs_of_velocity_bins μ c hc E
    ρ ζ hρ hζ π C amplitude dimension hcap
  exact prepare_original_spatial_cap_source μ ν c hc E hE ht hρ hζ hcut hC hamp hdim hfinite
    (fun world => π {v | parameterCode ρ v=parameterVelocityHeader world})
    (fun r fine => π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=parameterVelocityHeader fine})
    hcoarse hfine

end Jets2
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
