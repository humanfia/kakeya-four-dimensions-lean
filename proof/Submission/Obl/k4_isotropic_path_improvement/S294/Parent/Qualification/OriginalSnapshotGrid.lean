-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalSnapshotGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalSnapshotGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalSnapshotCubes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

/-! # One original cut supplies every scalar snapshot width

A finite dyadic query grid covers the continuum of widths above the
scalar cutoff. The exact original prior appears on every time fiber;
only current incidence ceilings are requested on the right.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Prepare all original scalar cube numerators from the finite original
entry grid. Original coefficient atoms and original priors are retained.
The fixed factor625 pays only the dyadic cube cover. -/
theorem prepare_original_snapshot_grid {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ×ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    {ρ ζ cut : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ) (hcut : 0 < cut)
    (hfinite : ∀ n : ℕ, n ≤ parameterLevel ζ →
      ((fun z : Λ×ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite) :
    ∃ R : Set (Λ×ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ ((parameterLevel ζ+1:ℕ):ℝ≥0∞)*
        ENNReal.ofReal (cut*zoomBlockVisitConstant)*ν univ ∧
      ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ (world : Fin 7 → ℤ)
        (D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ))),
        (∀ block∈D, block.1=world) →
        ∀ (C amplitude : ℝ) (weight : ℝ≥0∞),
        (∀ cell : Fin 4 → ℤ,
          (μ.restrict E) {z |
            canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
            originalZoomBlock c ρ (dyadicParameterWidth (parameterLevel q)) z.1∈D} ≤
            ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*amplitude)*weight) →
        ∀ (t a : ℝ) (b : Fin 2 → ℝ),
          ν {l | (l,t)∈R ∧
            originalZoomBlock c ρ (dyadicParameterWidth (parameterLevel q)) l∈D ∧
            InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
            625*(ENNReal.ofReal (C*amplitude/cut)*weight) := by
  let I := Fin (parameterLevel ζ+1)
  have hs1 (i : I) : dyadicParameterWidth i ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨R,hR,hsub,hloss,hcaps⟩ := prepare_original_parameter_snapshots
    μ ν c hc E hE ht (fun _ : I => ρ) (fun i : I => dyadicParameterWidth i)
    (fun _ : I => cut) (fun _ => hρ) (fun i => dyadicParameterWidth_pos i)
    hs1 (fun _ => hcut) (fun i => hfinite i (Nat.le_of_lt_succ i.isLt))
  refine ⟨R,hR,hsub,?_,?_⟩
  · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,I,mul_assoc]
      using hloss
  · intro q hζq hq1 world D hDworld C amplitude weight hcurrent t a b
    let i : I := ⟨parameterLevel q,parameterLevel_below_floor hζ hζq hq1⟩
    have hq0 := hζ.trans_le hζq
    have hqs : q ≤ (2:ℝ)*dyadicParameterWidth (parameterLevel q) := by
      linarith [(parameterLevel_width q hq0 hq1).1]
    have h := original_zoom_cube_of_snapshot_cells_multiple ν c R ρ
      (s := dyadicParameterWidth (parameterLevel q)) (q := q)
      (dyadicParameterWidth_pos _) 2 hqs world D hDworld t a b
      (ENNReal.ofReal (C*amplitude/cut)*weight) ?_
    · norm_num at h
      exact h
    · intro cell
      exact hcaps i t cell D C amplitude weight (hcurrent cell)

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
