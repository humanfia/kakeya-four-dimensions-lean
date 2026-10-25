/- Adapted from same-tree o168/x0569-o196port, commit c22aeb8a. -/
/-
Adapted from: here:o168 (session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/NodeRounding.lean), renamed into the o196
namespace. Its own provenance comments are retained below.
-/
import Mathlib

/-!
# Choosing a grid node for every tangent depth

If the layer depths of a finite path satisfy `(a + 1) Δ − η ≤ depth a ≤ (a + 1) Δ`, every
original depth `sc * s ∈ [Δ, (m + 1) Δ]` has a node within `Δ + η`, so in tangent units
`|depth (node s) / sc − s| ≤ (Δ + η) / sc`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

/-- **A node for every tangent depth in range.** -/
theorem exists_node {m : ℕ} {Δ η sc : ℝ} (hΔ : 0 < Δ) (hη : 0 ≤ η) (hsc : 0 < sc)
    (depth : Fin (m + 1) → ℝ)
    (hdepth : ∀ a : Fin (m + 1), ((a : ℕ) + 1 : ℝ) * Δ - η ≤ depth a ∧
      depth a ≤ ((a : ℕ) + 1 : ℝ) * Δ) :
    ∃ node : ℝ → Fin (m + 1), ∀ s : ℝ, Δ ≤ sc * s → sc * s ≤ ((m : ℝ) + 1) * Δ →
      |depth (node s) / sc - s| ≤ (Δ + η) / sc := by
  classical
  let idx : ℝ → ℕ := fun s => min (⌊sc * s / Δ⌋₊ - 1) m
  refine ⟨fun s => ⟨idx s, Nat.lt_succ_of_le (min_le_right _ _)⟩, ?_⟩
  intro s hs1 hs2
  set x := sc * s / Δ with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hΔ]; linarith
  have hx2 : x ≤ (m : ℝ) + 1 := by rw [hx, div_le_iff₀ hΔ]; linarith
  have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hflx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  -- the chosen index and its real value
  set a := idx s with ha
  have ha_le : (a : ℝ) + 1 ≤ x + 1 := by
    have : a ≤ ⌊x⌋₊ - 1 := min_le_left _ _
    have : (a : ℝ) ≤ (⌊x⌋₊ : ℝ) - 1 := by
      have h' : ((⌊x⌋₊ - 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hfl1, Nat.cast_one]
      calc (a : ℝ) ≤ ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by exact_mod_cast this
        _ = _ := h'
    linarith
  have ha_ge : x - 1 ≤ (a : ℝ) + 1 := by
    by_cases hmin : ⌊x⌋₊ - 1 ≤ m
    · have : a = ⌊x⌋₊ - 1 := min_eq_left hmin
      have h' : (a : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
        rw [this, Nat.cast_sub hfl1, Nat.cast_one]
      linarith
    · push Not at hmin
      have : a = m := min_eq_right hmin.le
      rw [this]; linarith
  have hd := hdepth ⟨a, Nat.lt_succ_of_le (min_le_right _ _)⟩
  simp only at hd
  obtain ⟨hd1, hd2⟩ := hd
  -- |depth - sc s| ≤ Δ + η
  have hsc_s : sc * s = x * Δ := by rw [hx]; field_simp
  have habs : |depth ⟨a, Nat.lt_succ_of_le (min_le_right _ _)⟩ - sc * s| ≤ Δ + η := by
    rw [abs_le]
    constructor
    · nlinarith [hsc_s]
    · nlinarith [hsc_s]
  have : depth ⟨a, Nat.lt_succ_of_le (min_le_right _ _)⟩ / sc - s =
      (depth ⟨a, Nat.lt_succ_of_le (min_le_right _ _)⟩ - sc * s) / sc := by
    field_simp
  rw [this, abs_div, abs_of_pos hsc]
  exact div_le_div_of_nonneg_right habs hsc.le

end Submission.Obl.k4_scalar_guarded_entropic_path
