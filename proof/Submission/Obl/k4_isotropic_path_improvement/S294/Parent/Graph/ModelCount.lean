-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.ModelCount, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/ModelCount.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). The hereditary count input of `model_velocity_rows` from
finite tables of product codes `(Fin 3 → ℤ) × ℤ` (the form produced by
`HereditaryClockSupport.exists_hereditary_support`) in the model's own base
`(t, c3 + c4 t, c5 + c6 t)` and signal: the two codes are joined by
`Fin.snoc`, and an empty table is padded by one code.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.ModelRows
import Submission.Lib.K4ParentSignalPreparation.Census

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census

noncomputable section

/-- The model's base point `(t, c3 + c4 t, c5 + c6 t)` of an incidence. -/
def modelBase (pm : Qualification.PhysicalModel) (z : Ev) : Fin 3 → ℝ :=
  ![z.2, pm.position z.1 1 + z.2 * pm.velocity z.1 1, pm.position z.1 2 + z.2 * pm.velocity z.1 2]

/-- The model's signal at an incidence. -/
def modelHeight (pm : Qualification.PhysicalModel) (z : Ev) : ℝ := pm.signalValue z.1 z.2

/-- On assigned lines the model code is the joined product code. -/
theorem modelCode_eq_snoc (pm : Qualification.PhysicalModel) (b h : ℝ) {z : Ev}
    (hz : z.1 ∈ pm.assigned) :
    modelCode pm b h z = Fin.snoc (gridCode (modelBase pm) (modelHeight pm) b h z).1
      (gridCode (modelBase pm) (modelHeight pm) b h z).2 := by
  rw [modelCode_apply pm b h hz]
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last, gridCode, modelHeight]
    rfl
  · simp only [Fin.snoc_castSucc, gridCode, modelBase]
    fin_cases i <;> rfl

/-- **The count input of `model_velocity_rows` from product-code tables.** -/
theorem model_count_of_tables (pm : Qualification.PhysicalModel) (current : Set Ev)
    (hcur : ∀ z ∈ current, z.1 ∈ pm.assigned)
    {baseMesh hidden coarse Kc dim : ℝ} (hb : 0 < baseMesh) (hh : 0 < hidden)
    (hcb : baseMesh ≤ coarse) (hch : hidden ≤ coarse) (hK1 : 1 ≤ Kc) (hdim : 0 ≤ dim)
    (htab : ∀ q : (Fin 3 → ℤ) × ℤ, ∃ F : Finset ((Fin 3 → ℤ) × ℤ),
      (F.card : ℝ) ≤ Kc * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dim ∧
      ∀ z ∈ current, gridCode (modelBase pm) (modelHeight pm) coarse coarse z = q →
        gridCode (modelBase pm) (modelHeight pm) baseMesh hidden z ∈ F)
    (q4 : Fin 4 → ℤ) :
    ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ Kc * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dim ∧
      ∀ z ∈ current, modelCode pm coarse coarse z = q4 → modelCode pm baseMesh hidden z ∈ S := by
  classical
  obtain ⟨F, hF, hFmem⟩ := htab (Fin.init q4, q4 (Fin.last 3))
  let S0 : Finset (Fin 4 → ℤ) := F.image (fun k => Fin.snoc k.1 k.2)
  have hone : (1 : ℝ) ≤ Kc * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dim := by
    have h1 : 1 ≤ coarse / baseMesh := (one_le_div hb).mpr hcb
    have h2 : 1 ≤ coarse / hidden := (one_le_div hh).mpr hch
    have h3 : 1 ≤ (coarse / baseMesh) ^ 3 := one_le_pow₀ h1
    have h4 : 1 ≤ (coarse / hidden) ^ dim := Real.one_le_rpow h2 hdim
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ Kc * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dim := by gcongr
  have hmem : ∀ z ∈ current, modelCode pm coarse coarse z = q4 →
      modelCode pm baseMesh hidden z ∈ S0 := by
    intro z hz hq
    have hzA := hcur z hz
    rw [modelCode_eq_snoc pm _ _ hzA] at hq ⊢
    have hq' : gridCode (modelBase pm) (modelHeight pm) coarse coarse z =
        (Fin.init q4, q4 (Fin.last 3)) := by
      rw [← hq]
      ext
      · simp [Fin.init_snoc]
      · dsimp only
        exact (Fin.snoc_last (α := fun _ => ℤ) _ _).symm
    exact Finset.mem_image_of_mem _ (hFmem z hz hq')
  by_cases hne : S0.Nonempty
  · refine ⟨S0, hne, ?_, hmem⟩
    exact (Nat.cast_le.mpr Finset.card_image_le).trans hF
  · refine ⟨insert 0 S0, Finset.insert_nonempty _ _, ?_, fun z hz hq =>
      Finset.mem_insert_of_mem (hmem z hz hq)⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, insert_empty_eq, Finset.card_singleton, Nat.cast_one]
    exact hone

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
