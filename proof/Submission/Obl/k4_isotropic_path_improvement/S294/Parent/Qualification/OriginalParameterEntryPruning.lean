-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalParameterEntryPruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalParameterEntryPruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomBlockVisits
import Submission.Obl.k4_scalar_grid_parameter_preparation.SparseEntryPruning

/-! # Localize full original parameter priors in the actual incidence law

The accepted sparse-entry pruning theorem is applied to the actual canonical
cell menus. Their C/s bound cancels the time length s in each threshold.
No full-prior snapshot ceiling is assumed, and all tested scales share one
final restriction of the incidence law.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Original coefficient blocks have small total cell-entry cost even
when their absolute intercepts and their number are arbitrarily large. -/
theorem prepare_original_parameter_cell_entries {Λ σ : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (ρ s cut : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hcut : ∀ i, 0 ≤ cut i)
    (hfinite : ∀ i, ((fun z : Λ × ℝ => originalZoomBlock c (ρ i) (s i) z.1) '' E).Finite) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, ENNReal.ofReal (cut i * zoomBlockVisitConstant)) * ν univ ∧
      ∀ i z, z∈R →
        ENNReal.ofReal (cut i * s i) *
          ν {l | originalZoomBlock c (ρ i) (s i) l = originalZoomBlock c (ρ i) (s i) z.1} <
        μ (R ∩ {y | originalZoomBlock c (ρ i) (s i) y.1 =
          originalZoomBlock c (ρ i) (s i) z.1 ∧
          canonicalZoomCell c (ρ i) (s i) y = canonicalZoomCell c (ρ i) (s i) z}) := by
  classical
  let carrier := fun i => (hfinite i).toFinset
  let κ := fun i => ↥(carrier i)
  let A := fun i (j : κ i) => {l | originalZoomBlock c (ρ i) (s i) l = j.val}
  have hblock (i) : Measurable (originalZoomBlock c (ρ i) (s i)) :=
    (((measurable_parameterCode (ρ i)).comp hc).prodMk
      ((measurable_parameterCode (ρ i*s i)).comp hc))
  have hA (i) (j : κ i) : MeasurableSet (A i j) :=
    hblock i (measurableSet_singleton j.val)
  have hdisj (i) : Pairwise fun (j j' : κ i) => Disjoint (A i j) (A i j') := by
    intro j j' hne
    exact disjoint_left.mpr fun l hl hl' => hne (Subtype.ext (hl.symm.trans hl'))
  choose menus hmenus hcover using fun i =>
    original_zoom_block_cell_lists E c (ρ i) (s i) (hρ i) (hs i) (hs1 i) ht
  let C := fun i (j : κ i) (q : Fin 4 → ℤ) =>
    {z : Λ × ℝ | originalZoomBlock c (ρ i) (s i) z.1 = j.val ∧
      canonicalZoomCell c (ρ i) (s i) z = q}
  have hC (i) (j : κ i) (q : Fin 4 → ℤ) : MeasurableSet (C i j q) :=
    (((hblock i).comp measurable_fst) (measurableSet_singleton j.val)).inter
      ((measurable_canonicalZoomCell hc (ρ i) (s i)) (measurableSet_singleton q))
  have hcount (i) (j : κ i) :
      ((menus i j.val).card : ENNReal) ≤ ENNReal.ofReal (zoomBlockVisitConstant/s i) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hmenus i j.val)
  obtain ⟨R,hR,hsub,hloss,hfloor⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.multiscale_sparse_prior_entry_pruning
      κ μ ν A hA hdisj (fun i j => menus i j.val) C (fun i j q _ => hC i j q)
      (fun i => ENNReal.ofReal (cut i*s i))
      (fun i => ENNReal.ofReal (zoomBlockVisitConstant/s i)) hcount hE
  have hcancel (i) :
      ENNReal.ofReal (cut i*s i) * ENNReal.ofReal (zoomBlockVisitConstant/s i) =
        ENNReal.ofReal (cut i*zoomBlockVisitConstant) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (hcut i) (hs i).le)]
    congr 1
    field_simp [ne_of_gt (hs i)]
  refine ⟨R,hR,hsub,by simpa only [hcancel] using hloss,?_⟩
  intro i z hz
  have hzE := hsub hz
  have hzcarrier : originalZoomBlock c (ρ i) (s i) z.1 ∈ carrier i :=
    (hfinite i).mem_toFinset.mpr ⟨z,hzE,rfl⟩
  let j : κ i := ⟨originalZoomBlock c (ρ i) (s i) z.1,hzcarrier⟩
  have hcell := hcover i z hzE
  obtain hempty | hf := hfloor i j (canonicalZoomCell c (ρ i) (s i) z) hcell
  · have hzmem : z∈R ∩ C i j (canonicalZoomCell c (ρ i) (s i) z) := ⟨hz,rfl,rfl⟩
    rw [hempty] at hzmem
    exact hzmem.elim
  · exact hf

/-- Dyadic nesting identifies each tagged prior with its full original
fine-bin prior, retaining every original trajectory tag. -/
theorem original_zoom_blocks_finite_of_fine {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ)
    (hfinite : ((fun z : Λ × ℝ => parameterCode (ρ*dyadicParameterWidth n) (c z.1)) '' E).Finite) :
    ((fun z : Λ × ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite := by
  apply (hfinite.image (fun q => (coarsenParameterCode n q,q))).subset
  rintro b ⟨z,hz,rfl⟩
  refine ⟨parameterCode (ρ*dyadicParameterWidth n) (c z.1),⟨z,hz,rfl⟩,?_⟩
  exact Prod.ext (coarsen_parameterCode ρ hρ n (c z.1)) rfl

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
