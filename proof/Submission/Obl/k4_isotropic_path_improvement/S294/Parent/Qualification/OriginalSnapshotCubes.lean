-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalSnapshotCubes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalSnapshotCubes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalSnapshotPreparation

/-! # Original scalar cubes from current entry caps

The spatial cube is expressed in the exact original parameter zoom.
The current incidence cap and original prior entry floor have the same
time factor, which cancels before the fixed geometric cube cover.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal
noncomputable section

/-- Canonical original time-fiber caps control the exact cubes used by
scalar-normal spatial estimates, inside any fixed original world. -/
theorem original_zoom_cube_of_snapshot_cells_multiple {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (R : Set (Λ×ℝ))
    (ρ : ℝ) {s q : ℝ} (hs : 0 < s)
    (multiple : ℕ) (hq : q ≤ (multiple:ℝ)*s) (world : Fin 7 → ℤ)
    (D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ)))
    (hDworld : ∀ block∈D, block.1=world)
    (t a : ℝ) (b : Fin 2 → ℝ) (bound : ℝ≥0∞)
    (hcap : ∀ q : Fin 4 → ℤ,
      ν {l | (l,t)∈R ∧ canonicalZoomCell c ρ s (l,t)=q ∧ originalZoomBlock c ρ s l∈D} ≤ bound) :
    ν {l | (l,t)∈R ∧ originalZoomBlock c ρ s l∈D ∧
      InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
        ((2*multiple+1:ℕ):ℝ≥0∞)^4*bound := by
  let T := {l | (l,t)∈R ∧ originalZoomBlock c ρ s l∈D}
  let A := {l | (l,t)∈R ∧ originalZoomBlock c ρ s l∈D ∧
    InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q}
  let x := fun l => zpos (canonicalZoomCoefficients c ρ l) t
  have hbox (l : Λ) (hl : l∈A) (j : Fin 4) : |x l j-(![t,a,b 0,b 1]) j| ≤ (multiple:ℝ)*s := by
    have hw : parameterCode ρ (c l)=world := hDworld _ hl.2.1
    have heq : canonicalZoomCoefficients c ρ l=
        zoomCoefficients ρ (parameterCenter ρ world) (c l) := by
      simp only [canonicalZoomCoefficients,hw]
    have hx : zx (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t∈Ico a (a+q) :=
      hl.2.2.1
    have hy := hl.2.2.2
    dsimp only [x]
    rw [heq]
    fin_cases j
    · change |t-t| ≤ (multiple:ℝ)*s
      simp only [sub_self,abs_zero]
      positivity
    · change |zx (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t-a| ≤ (multiple:ℝ)*s
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    · change |zy (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t 0-b 0| ≤ (multiple:ℝ)*s
      have hh := hy 0
      rw [abs_of_nonneg (by linarith [hh.1])]
      linarith [hh.2]
    · change |zy (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t 1-b 1| ≤ (multiple:ℝ)*s
      have hh := hy 1
      rw [abs_of_nonneg (by linarith [hh.1])]
      linarith [hh.2]
  have h := snapshot_cube_cap_of_cell_caps_multiple ν x A T (fun _ hl => ⟨hl.1,hl.2.1⟩)
    ![t,a,b 0,b 1] hs multiple hbox bound ?_
  · simpa only [Fintype.card_fin] using h
  · intro q
    convert hcap q using 2
    ext l
    simp only [T,mem_inter_iff,mem_ofPred_eq,canonicalZoomCell,x]
    tauto


/-- A canonical mesh at the tested cube width costs only a fixed factor. -/
theorem original_zoom_cube_of_snapshot_cells {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (R : Set (Λ×ℝ))
    (ρ : ℝ) {s : ℝ} (hs : 0 < s) (world : Fin 7 → ℤ)
    (D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ)))
    (hDworld : ∀ block∈D, block.1=world)
    (t a : ℝ) (b : Fin 2 → ℝ) (bound : ℝ≥0∞)
    (hcap : ∀ q : Fin 4 → ℤ,
      ν {l | (l,t)∈R ∧ canonicalZoomCell c ρ s (l,t)=q ∧ originalZoomBlock c ρ s l∈D} ≤ bound) :
    ν {l | (l,t)∈R ∧ originalZoomBlock c ρ s l∈D ∧
      InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b s} ≤
        81*bound := by
  have h := original_zoom_cube_of_snapshot_cells_multiple ν c R ρ (q := s) hs
    1 (by simp only [Nat.cast_one,one_mul,le_refl]) world D hDworld t a b bound hcap
  norm_num at h
  exact h

/-- Full original parameter-entry floors and current canonical incidence
caps supply the exact original zoomed cube numerator. No prior snapshot
bound is assumed. -/
theorem original_zoom_cube_from_current_entries {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (μ : Measure (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (R : Set (Λ×ℝ)) (ρ : ℝ) {s cut C amplitude : ℝ}
    (hs : 0 < s) (hcut : 0 < cut) (world : Fin 7 → ℤ)
    (D : Set ((Fin 7 → ℤ) × (Fin 7 → ℤ)))
    (hDworld : ∀ block∈D, block.1=world)
    (hfloor : ∀ z∈R, ENNReal.ofReal (cut*s)*
      ν {l | originalZoomBlock c ρ s l=originalZoomBlock c ρ s z.1} ≤
      μ {w | originalZoomBlock c ρ s w.1=originalZoomBlock c ρ s z.1 ∧
        canonicalZoomCell c ρ s w=canonicalZoomCell c ρ s z})
    (weight : ℝ≥0∞)
    (hcap : ∀ q, μ {z | canonicalZoomCell c ρ s z=q ∧ originalZoomBlock c ρ s z.1∈D} ≤
      ENNReal.ofReal (C*s*amplitude)*weight)
    (t a : ℝ) (b : Fin 2 → ℝ) :
    ν {l | (l,t)∈R ∧ originalZoomBlock c ρ s l∈D ∧
      InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b s} ≤
        81*(ENNReal.ofReal (C*amplitude/cut)*weight) := by
  have hblock : Measurable (originalZoomBlock c ρ s) :=
    (((measurable_parameterCode ρ).comp hc).prodMk
      ((measurable_parameterCode (ρ*s)).comp hc))
  apply original_zoom_cube_of_snapshot_cells ν c R ρ hs world D hDworld t a b
    (ENNReal.ofReal (C*amplitude/cut)*weight)
  intro q
  exact original_cell_snapshot_cap ν μ (originalZoomBlock c ρ s) hblock
    (canonicalZoomCell c ρ s) (measurable_canonicalZoomCell hc ρ s) R hcut hs hfloor
    t q D weight (hcap q)

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
