-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Dyadic, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Dyadic.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Dyadic.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Dyadic.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Mathlib

set_option autoImplicit false

/-!
# Dyadic intervals

Copied from this LOT tree: o229, session x0801, branch `x0801` at `ec0250f0`, `Jets/Dyadic.lean`
(independent of `j`; only the namespace changed).

`dI n j = [j 2⁻ⁿ, (j+1) 2⁻ⁿ)`, its subintervals at a finer level, covering and disjointness.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

/-- The half-open dyadic interval `[j 2⁻ⁿ, (j+1) 2⁻ⁿ)`. -/
def dI (n : ℕ) (j : ℤ) : Set ℝ := Ico ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n)

/-- Index of the `i`-th subinterval at level `m ≥ n`. -/
def subIdx (n m : ℕ) (j : ℤ) (i : ℕ) : ℤ := j * 2 ^ (m - n) + i

theorem measurableSet_dI (n : ℕ) (j : ℤ) : MeasurableSet (dI n j) := measurableSet_Ico

theorem volume_dI (n : ℕ) (j : ℤ) : volume (dI n j) = ENNReal.ofReal ((2 ^ n)⁻¹) := by
  rw [dI, Real.volume_Ico]; congr 1; field_simp; ring

theorem dI_sub {n m : ℕ} (h : n ≤ m) (j : ℤ) {i : ℕ} (hi : i < 2 ^ (m - n)) :
    dI m (subIdx n m j i) ⊆ dI n j := by
  intro x ⟨h1, h2⟩
  have hpow : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hq : (0 : ℝ) < 2 ^ (m - n) := by positivity
  have hi' : (i : ℝ) + 1 ≤ 2 ^ (m - n) := by exact_mod_cast hi
  simp only [subIdx] at h1 h2
  push_cast at h1 h2
  rw [hpow] at h1 h2
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  constructor
  · calc (j : ℝ) / 2 ^ n = ((j : ℝ) * 2 ^ (m - n)) / ((2 : ℝ) ^ n * 2 ^ (m - n)) := by field_simp
      _ ≤ ((j : ℝ) * 2 ^ (m - n) + i) / ((2 : ℝ) ^ n * 2 ^ (m - n)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ x := h1
  · calc x < ((j : ℝ) * 2 ^ (m - n) + i + 1) / ((2 : ℝ) ^ n * 2 ^ (m - n)) := h2
      _ ≤ ((j : ℝ) * 2 ^ (m - n) + 2 ^ (m - n)) / ((2 : ℝ) ^ n * 2 ^ (m - n)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = ((j : ℝ) + 1) / 2 ^ n := by field_simp

theorem dI_cover {n m : ℕ} (h : n ≤ m) (j : ℤ) :
    dI n j = ⋃ i ∈ Finset.range (2 ^ (m - n)), dI m (subIdx n m j i) := by
  apply Subset.antisymm
  · intro x ⟨h1, h2⟩
    have hpow : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by
      rw [← pow_add, Nat.add_sub_cancel' h]
    have hm : (0 : ℝ) < 2 ^ m := by positivity
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    set z := ⌊x * 2 ^ m⌋
    have hz1 : (z : ℝ) ≤ x * 2 ^ m := Int.floor_le _
    have hz2 : x * 2 ^ m < z + 1 := Int.lt_floor_add_one _
    have hlo : j * 2 ^ (m - n) ≤ z := by
      apply Int.le_floor.mpr
      push_cast
      rw [div_le_iff₀ hp] at h1
      rw [hpow]; nlinarith [show (0:ℝ) < 2 ^ (m - n) by positivity]
    have hhi : z < j * 2 ^ (m - n) + 2 ^ (m - n) := by
      have : x * 2 ^ m < ((j : ℝ) + 1) * 2 ^ (m - n) := by
        rw [lt_div_iff₀ hp] at h2
        rw [hpow]; nlinarith [show (0:ℝ) < 2 ^ (m - n) by positivity]
      have : (z : ℝ) < (j : ℝ) * 2 ^ (m - n) + 2 ^ (m - n) := by linarith
      exact_mod_cast this
    set i := (z - j * 2 ^ (m - n)).toNat
    have hi : (i : ℤ) = z - j * 2 ^ (m - n) := Int.toNat_of_nonneg (by omega)
    have hcast : ((2 ^ (m - n) : ℕ) : ℤ) = (2 : ℤ) ^ (m - n) := by push_cast; ring
    have hilt : i < 2 ^ (m - n) := by
      have : (i : ℤ) < ((2 ^ (m - n) : ℕ) : ℤ) := by rw [hcast, hi]; omega
      exact_mod_cast this
    simp only [mem_iUnion, Finset.mem_range, exists_prop]
    refine ⟨i, hilt, ?_, ?_⟩
    · simp only [subIdx]
      rw [div_le_iff₀ hm]
      have : ((j * 2 ^ (m - n) + (i : ℤ) : ℤ) : ℝ) = (z : ℝ) := by rw [hi]; ring
      push_cast at this ⊢
      linarith
    · simp only [subIdx]
      rw [lt_div_iff₀ hm]
      have : ((j * 2 ^ (m - n) + (i : ℤ) : ℤ) : ℝ) = (z : ℝ) := by rw [hi]; ring
      push_cast at this ⊢
      linarith
  · intro x hx
    simp only [mem_iUnion, Finset.mem_range, exists_prop] at hx
    obtain ⟨i, hi, hx⟩ := hx
    exact dI_sub h j hi hx

theorem dI_disjoint (m : ℕ) {j j' : ℤ} (hjj : j ≠ j') : Disjoint (dI m j) (dI m j') := by
  rw [Set.disjoint_left]
  intro x ⟨a1, a2⟩ ⟨b1, b2⟩
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_iff₀ hm] at a1 b1
  rw [lt_div_iff₀ hm] at a2 b2
  have h1 : (j : ℝ) < j' + 1 := by linarith
  have h2 : (j' : ℝ) < j + 1 := by linarith
  have h1' : j < j' + 1 := by exact_mod_cast h1
  have h2' : j' < j + 1 := by exact_mod_cast h2
  omega

theorem subIdx_injective (n m : ℕ) (j : ℤ) : Function.Injective (subIdx n m j) := by
  intro i i' h
  simp only [subIdx] at h
  omega

theorem abs_sub_lt_of_mem_dI {n : ℕ} {j : ℤ} {x y : ℝ} (hx : x ∈ dI n j) (hy : y ∈ dI n j) :
    |x - y| < (2 ^ n)⁻¹ := by
  obtain ⟨a1, a2⟩ := hx
  obtain ⟨b1, b2⟩ := hy
  have : ((j : ℝ) + 1) / 2 ^ n - (j : ℝ) / 2 ^ n = (2 ^ n)⁻¹ := by field_simp; ring
  rw [abs_lt]; constructor <;> linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
