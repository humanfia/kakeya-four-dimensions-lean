-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.SnapshotCellCubes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/SnapshotCellCubes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Mathlib

/-! # Fixed-time cube caps from canonical cell caps -/
set_option autoImplicit false
namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- A radius-m*s box meets at most 2*m+1 bins per coordinate. -/
theorem snapshot_cube_cap_of_cell_caps_multiple {Λ ι : Type*} [MeasurableSpace Λ]
    [Fintype ι] [DecidableEq ι]
    (ν : Measure Λ) (x : Λ → ι → ℝ) (A T : Set Λ) (hAT : A⊆T)
    (corner : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (multiple : ℕ)
    (hbox : ∀ l∈A, ∀ j, |x l j-corner j| ≤ (multiple:ℝ)*s)
    (bound : ℝ≥0∞)
    (hcap : ∀ q : ι → ℤ, ν (T ∩ {l | (fun j => (⌊x l j/s⌋ : ℤ))=q}) ≤ bound) :
    ν A ≤ ((2*multiple+1:ℕ):ℝ≥0∞)^Fintype.card ι*bound := by
  classical
  let bins : ι → Finset ℤ := fun j => Finset.Icc
    ((⌊corner j/s⌋ : ℤ)-(multiple:ℤ)) ((⌊corner j/s⌋ : ℤ)+(multiple:ℤ))
  let menus := Fintype.piFinset bins
  have hknown (l : Λ) (hl : l∈A) : (fun j => (⌊x l j/s⌋ : ℤ))∈menus := by
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Finset.mem_Icc.mpr
    have hj := abs_le.mp (hbox l hl j)
    have hlo : corner j-(multiple:ℝ)*s ≤ x l j := by linarith
    have hhi : x l j ≤ corner j+(multiple:ℝ)*s := by linarith
    have hlo' := Int.floor_mono (div_le_div_of_nonneg_right hlo hs.le)
    have hhi' := Int.floor_mono (div_le_div_of_nonneg_right hhi hs.le)
    have heqlo : (corner j-(multiple:ℝ)*s)/s=corner j/s-(multiple:ℝ) := by field_simp
    have heqhi : (corner j+(multiple:ℝ)*s)/s=corner j/s+(multiple:ℝ) := by field_simp
    rw [heqlo,Int.floor_sub_natCast] at hlo'
    rw [heqhi,Int.floor_add_natCast] at hhi'
    exact ⟨hlo',hhi'⟩
  have hcard : menus.card=(2*multiple+1)^Fintype.card ι := by
    have hb (j : ι) : (bins j).card=2*multiple+1 := by
      dsimp only [bins]
      rw [Int.card_Icc]
      omega
    dsimp only [menus]
    rw [Fintype.card_piFinset]
    simp only [hb,Finset.prod_const,Finset.card_univ]
  have hcover : A⊆⋃ q∈menus, T ∩ {l | (fun j => (⌊x l j/s⌋ : ℤ))=q} := by
    intro l hl
    exact mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨hknown l hl,⟨hAT hl,rfl⟩⟩⟩
  calc
    ν A ≤ ν (⋃ q∈menus, T ∩ {l | (fun j => (⌊x l j/s⌋ : ℤ))=q}) := measure_mono hcover
    _ ≤ ∑ q∈menus, ν (T ∩ {l | (fun j => (⌊x l j/s⌋ : ℤ))=q}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q∈menus, bound := Finset.sum_le_sum (fun q _ => hcap q)
    _ = ((2*multiple+1:ℕ):ℝ≥0∞)^Fintype.card ι*bound := by
      rw [Finset.sum_const,nsmul_eq_mul,hcard]
      simp

/-- A radius-s box meets at most three bins per coordinate. -/
theorem snapshot_cube_cap_of_cell_caps {Λ ι : Type*} [MeasurableSpace Λ]
    [Fintype ι] [DecidableEq ι]
    (ν : Measure Λ) (x : Λ → ι → ℝ) (A T : Set Λ) (hAT : A⊆T)
    (corner : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (hbox : ∀ l∈A, ∀ j, |x l j-corner j| ≤ s)
    (bound : ℝ≥0∞)
    (hcap : ∀ q : ι → ℤ, ν (T ∩ {l | (fun j => (⌊x l j/s⌋ : ℤ))=q}) ≤ bound) :
    ν A ≤ (3:ℝ≥0∞)^Fintype.card ι*bound := by
  simpa using snapshot_cube_cap_of_cell_caps_multiple
    ν x A T hAT corner hs 1 (by simpa only [Nat.cast_one,one_mul] using hbox) bound hcap

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
