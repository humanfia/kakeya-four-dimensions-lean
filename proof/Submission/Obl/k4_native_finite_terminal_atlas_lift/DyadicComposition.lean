/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/DyadicComposition.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Definitions

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- Concatenate parent and child dyadic block digits. -/
def compositeBlock {T U : ℕ} (j : Fin (2 ^ T)) (k : Fin (2 ^ U)) : Fin (2 ^ (T + U)) :=
  ⟨j.val * 2 ^ U + k.val, by
    rw [pow_add]
    calc
      j.val * 2 ^ U + k.val < j.val * 2 ^ U + 2 ^ U := Nat.add_lt_add_left k.isLt _
      _ = (j.val + 1) * 2 ^ U := by ring
      _ ≤ 2 ^ T * 2 ^ U := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr j.isLt)⟩

theorem compositeBlock_injective {T U : ℕ} {j j' : Fin (2 ^ T)} {k k' : Fin (2 ^ U)}
    (heq : compositeBlock j k = compositeBlock j' k') : j = j' ∧ k = k' := by
  have he := congrArg Fin.val heq
  change j.val * 2 ^ U + k.val = j'.val * 2 ^ U + k'.val at he
  have hU : 0 < 2 ^ U := by positivity
  have hd := congrArg (fun n => n / 2 ^ U) he
  have hm := congrArg (fun n => n % 2 ^ U) he
  rw [Nat.mul_comm j.val, Nat.mul_comm j'.val,
    Nat.mul_add_div hU, Nat.mul_add_div hU] at hd
  simp only [Nat.div_eq_of_lt k.isLt, Nat.div_eq_of_lt k'.isLt, Nat.add_zero] at hd
  simp [Nat.add_mod, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt k'.isLt] at hm
  exact ⟨Fin.ext hd, Fin.ext hm⟩

theorem compositeBlock_lower {T U : ℕ} (j : Fin (2 ^ T)) (k : Fin (2 ^ U)) :
    ((compositeBlock j k : ℕ) : ℝ) / (2 : ℝ) ^ (T + U) =
      (j : ℝ) / (2 : ℝ) ^ T + ((k : ℝ) / (2 : ℝ) ^ U) / (2 : ℝ) ^ T := by
  change ((j.val * 2 ^ U + k.val : ℕ) : ℝ) / (2 : ℝ) ^ (T + U) = _
  push_cast
  rw [pow_add]
  field_simp <;> ring

theorem compositeBlock_upper {T U : ℕ} (j : Fin (2 ^ T)) (k : Fin (2 ^ U)) :
    (((compositeBlock j k : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + U) =
      (j : ℝ) / (2 : ℝ) ^ T + (((k : ℝ) + 1) / (2 : ℝ) ^ U) / (2 : ℝ) ^ T := by
  change (((j.val * 2 ^ U + k.val : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + U) = _
  push_cast
  rw [pow_add]
  field_simp <;> ring

/-- The preimage of a concatenated old block is exactly the child block. -/
theorem compositeBlock_interval {T U : ℕ} (j : Fin (2 ^ T)) (k : Fin (2 ^ U)) (τ : ℝ) :
    (j : ℝ) / (2 : ℝ) ^ T + τ / (2 : ℝ) ^ T ∈
      Set.Icc (((compositeBlock j k : ℕ) : ℝ) / (2 : ℝ) ^ (T + U))
        ((((compositeBlock j k : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + U)) ↔
      τ ∈ Set.Icc ((k : ℝ) / (2 : ℝ) ^ U) (((k : ℝ) + 1) / (2 : ℝ) ^ U) := by
  rw [compositeBlock_lower, compositeBlock_upper]
  simp only [Set.mem_Icc, add_le_add_iff_left]
  exact and_congr (div_le_div_iff_of_pos_right (by positivity))
    (div_le_div_iff_of_pos_right (by positivity))

end Submission.Obl.k4_native_finite_terminal_atlas_lift
