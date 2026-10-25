-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/UniformGridRefinement.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_finite_forest_width_selection.ForestCombinatorics

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.UniformGridRefinement

open Submission.Obl.k4_finite_forest_width_selection

def coarseIndex (k i : ℕ) : ℕ := k * (i + 1) - 1

theorem coarseIndex_add_one (k : ℕ) (hk : 0 < k) (i : ℕ) :
    coarseIndex k i + 1 = k * (i + 1) := by
  have hpos : 0 < k * (i + 1) := Nat.mul_pos hk (Nat.succ_pos _)
  dsimp [coarseIndex]
  omega

theorem coarseIndex_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (coarseIndex k) := by
  intro i j hij
  have hmul : k * (i + 1) = k * (j + 1) := by
    rw [← coarseIndex_add_one k hk i, ← coarseIndex_add_one k hk j, hij]
  have heq := Nat.eq_of_mul_eq_mul_left hk hmul
  omega

theorem coarseIndex_monotone (k : ℕ) : Monotone (coarseIndex k) := by
  intro i j hij
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left k (Nat.add_le_add_right hij 1)) 1

/-- The old right endpoint in a uniformly refined grid. -/
def uniformIndex {m : ℕ} (k : ℕ) (hk : 0 < k) (i : Fin m) : Fin (m * k) :=
  ⟨k * (i.val + 1) - 1, by
    have hpos : 0 < k * (i.val + 1) := Nat.mul_pos hk (Nat.succ_pos _)
    have hle : k * (i.val + 1) ≤ m * k := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : i.val + 1 ≤ m)
    omega⟩

theorem uniformIndex_add_one {m : ℕ} (k : ℕ) (hk : 0 < k) (i : Fin m) :
    (uniformIndex k hk i).val + 1 = k * (i.val + 1) := by
  have hpos : 0 < k * (i.val + 1) := Nat.mul_pos hk (Nat.succ_pos _)
  dsimp [uniformIndex]
  omega

theorem uniformIndex_injective {m : ℕ} (k : ℕ) (hk : 0 < k) :
    Function.Injective (uniformIndex (m := m) k hk) := by
  intro i j hij
  have hmul : k * (i.val + 1) = k * (j.val + 1) := by
    rw [← uniformIndex_add_one k hk i, ← uniformIndex_add_one k hk j, hij]
  have heq := Nat.eq_of_mul_eq_mul_left hk hmul
  exact Fin.ext (by omega)

/-- Refinement preserves every old grid coordinate exactly. -/
theorem uniformIndex_coordinate {m : ℕ} (k : ℕ) (hk : 0 < k) (i : Fin m) :
    (((uniformIndex k hk i).val : ℝ) + 1) / ((m * k : ℕ) : ℝ) =
      ((i.val : ℝ) + 1) / (m : ℝ) := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hn : ((uniformIndex k hk i).val : ℝ) + 1 = (k : ℝ) * ((i.val : ℝ) + 1) := by
    exact_mod_cast uniformIndex_add_one k hk i
  rw [hn, Nat.cast_mul]
  field_simp

theorem uniformIndex_last {m : ℕ} (hm : 0 < m) (k : ℕ) (hk : 0 < k) :
    (uniformIndex (m := m) k hk ⟨m - 1, by omega⟩).val = m * k - 1 := by
  change k * (m - 1 + 1) - 1 = m * k - 1
  rw [Nat.sub_add_cancel hm, Nat.mul_comm]

/-- Any finite uniform grid has an arbitrarily fine uniform refinement. The
refinement factor is chosen before any path data. -/
theorem exists_fine_uniform_refinement {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    ∃ k : ℕ, 0 < k ∧ 1 / ((m * k : ℕ) : ℝ) ≤ a := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (1 / ((m : ℝ) * a)))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkpos : 0 < k := by exact_mod_cast (by linarith : (0 : ℝ) < k)
  have hma : 0 < (m : ℝ) * a := mul_pos (Nat.cast_pos.mpr hm) ha
  have hlarge : 1 < (k : ℝ) * ((m : ℝ) * a) :=
    (div_lt_iff₀ hma).mp ((le_max_right _ _).trans_lt hk)
  refine ⟨k, hkpos, (div_le_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hm hkpos))).mpr ?_⟩
  push_cast
  nlinarith

/-- Every transitive child-to-parent relation persists to any earlier ancestor.
The level calculation uses the accepted finite-forest kernel. -/
theorem forest_ancestor_relation {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (R : Fin C → Fin C → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ b, 0 < lev b → R b (par b))
    (b : Fin C) (i : ℕ) :
    R b (forestAncestor lev par b i) := by
  have aux : ∀ (n : ℕ) (b : Fin C), n ≤ lev b → R b (par^[n] b) := by
    intro n
    induction n with
    | zero => intro b _; simpa using hrefl b
    | succ n ih =>
      intro b hn
      have hb : 0 < lev b := by omega
      have hp := hpar b hb
      rw [Function.iterate_succ_apply]
      exact htrans _ _ _ (hstep b hb) (ih (par b) (by omega))
  simpa only [forestAncestor] using aux (lev b - i) b (Nat.sub_le _ _)

end Submission.Obl.k4_isotropic_path_improvement.Repair.UniformGridRefinement
