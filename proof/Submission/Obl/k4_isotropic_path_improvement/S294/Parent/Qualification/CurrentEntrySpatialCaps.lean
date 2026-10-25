-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentEntrySpatialCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CurrentEntrySpatialCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalSnapshotGrid

/-! # Simultaneous original spatial numerators from current incidences

One entry cut supplies every coarse and conditional fine original
spatial cube numerator. The current caps may use any original reference
weights. The scalar profile amplitude is retained multiplicatively.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- The current canonical cell ceilings supply all original cube
numerators used to normalize the scalar-normal AB and BC estimates. -/
theorem prepare_original_spatial_cap_source {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ×ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    {ρ ζ cut C amplitude dimension : ℝ}
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hcut : 0 < cut)
    (hC : 0 ≤ C) (hamp : 0 ≤ amplitude) (hdim : 0 ≤ dimension)
    (hfinite : ∀ n : ℕ, n ≤ parameterLevel ζ →
      ((fun z : Λ×ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite)
    (coarseWeight : (Fin 7 → ℤ) → ℝ≥0∞)
    (fineWeight : ℝ → (Fin 7 → ℤ) → ℝ≥0∞)
    (hcoarse : ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*coarseWeight world)
    (hfine : ∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ q : ℝ, ζ ≤ q → q ≤ r → ∀ world fine cell,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧ zoomParameterPiece ρ c r z.1=fine ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell} ≤
      ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
        (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)*fineWeight r fine) :
    ∃ R : Set (Λ×ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ ((parameterLevel ζ+1:ℕ):ℝ≥0∞)*
        ENNReal.ofReal (cut*zoomBlockVisitConstant)*ν univ ∧
      (∀ world (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ), ζ ≤ q → q ≤ 1 →
        ν {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
          ENNReal.ofReal ((625*C/cut)*(ρ*q)^((2:ℝ)+dimension)*amplitude)*coarseWeight world) ∧
      (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ world fine (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ),
        ζ ≤ q → q ≤ r →
        ν {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
          ENNReal.ofReal ((625*C/cut)*(ρ*q)^((2:ℝ)+dimension)*amplitude)*fineWeight r fine) := by
  obtain ⟨R,hR,hsub,hloss,hcaps⟩ := prepare_original_snapshot_grid μ ν c hc E hE ht
    hρ hζ hcut hfinite
  have hscale (q : ℝ) (hq : ζ ≤ q) (hq1 : q ≤ 1) (weight : ℝ≥0∞) :
      625*(ENNReal.ofReal (C*((ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)/cut)*weight) ≤
        ENNReal.ofReal ((625*C/cut)*(ρ*q)^((2:ℝ)+dimension)*amplitude)*weight := by
    have hq0 := hζ.trans_le hq
    have hw := (parameterLevel_width q hq0 hq1).2
    have hp : (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension) ≤
        (ρ*q)^((2:ℝ)+dimension) := Real.rpow_le_rpow
      (mul_nonneg hρ.le (dyadicParameterWidth_pos _).le)
      (mul_le_mul_of_nonneg_left hw hρ.le) (by linarith)
    have heq : (625:ℝ≥0∞)*ENNReal.ofReal
        (C*((ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)/cut)=
        ENNReal.ofReal ((625*C/cut)*(ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude) := by
      rw [show (625:ℝ≥0∞)=ENNReal.ofReal (625:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 625)]
      congr 1
      ring
    rw [←mul_assoc,heq]
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hamp
  refine ⟨R,hR,hsub,hloss,?_,?_⟩
  · intro world t a b q hq hq1
    let D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ)) := {block | block.1=world}
    have h := hcaps q hq hq1 world D (fun _ hd => hd) C
      ((ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)
      (coarseWeight world) ?_ t a b
    · have h' := h.trans (hscale q hq hq1 (coarseWeight world))
      convert h' using 2
      ext l
      simp only [D,originalZoomBlock,mem_ofPred_eq]
      tauto
    · intro cell
      simpa only [D,originalZoomBlock,mem_ofPred_eq,mul_assoc,and_comm] using
        hcoarse q hq hq1 world cell
  · intro r hr hr1 world fine t a b q hq hqr
    have hq1 := hqr.trans hr1
    have hq0 := hζ.trans_le hq
    have hn := parameterLevel_antitone_on_unit hq0 hqr hr1
    let D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ)) := {block | block.1=world ∧
      coarsenParameterCode (parameterLevel q-parameterLevel r) block.2=fine}
    have hD (l : Λ) : originalZoomBlock c ρ (dyadicParameterWidth (parameterLevel q)) l∈D ↔
        parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine := by
      dsimp only [D,originalZoomBlock,mem_ofPred_eq,zoomParameterPiece]
      rw [coarsen_nested_parameterCode ρ hρ hn]
    have h := hcaps q hq hq1 world D (fun _ hd => hd.1) C
      ((ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*amplitude)
      (fineWeight r fine) ?_ t a b
    · have h' := h.trans (hscale q hq hq1 (fineWeight r fine))
      convert h' using 2
      ext l
      simp only [hD,mem_ofPred_eq]
      tauto
    · intro cell
      simpa only [hD,mem_ofPred_eq,mul_assoc,and_assoc,and_left_comm,and_comm] using
        hfine r hr hr1 q hq hqr world fine cell

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
