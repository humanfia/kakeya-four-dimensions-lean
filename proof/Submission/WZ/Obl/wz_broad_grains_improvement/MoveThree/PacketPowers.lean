-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketPowers.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalPackets
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

noncomputable section

/-- Rounding the geometric confinement factor costs a fixed constant and
twelve powers in the anchor palette. -/
theorem natural_packet_palette_bound {δ b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) :
    ∃ A : ℕ, 1 ≤ A ∧ δ ^ (-b) ≤ A ∧
      (((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) ≤ 516 ^ 6 * δ ^ (-12 * b) := by
  let A : ℕ := ⌈δ ^ (-b)⌉₊
  have hp : 1 ≤ δ ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hb)
  have hA : δ ^ (-b) ≤ (A : ℝ) := Nat.le_ceil _
  have hA1 : 1 ≤ A := by exact_mod_cast hp.trans hA
  have hAup : (A : ℝ) ≤ 2 * δ ^ (-b) := by
    have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hδ.le (-b))
    dsimp only [A]
    linarith
  have hstep : (128 * (A : ℝ) ^ 2 + 1) ≤ 516 * (δ ^ (-b)) ^ 2 := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg A) hAup 2
    nlinarith [sq_nonneg (δ ^ (-b) - 1)]
  refine ⟨A, hA1, hA, ?_⟩
  calc
    _ = (128 * (A : ℝ) ^ 2 + 1) ^ 6 := by norm_cast
    _ ≤ (516 * (δ ^ (-b)) ^ 2) ^ 6 := pow_le_pow_left₀ (by positivity) hstep _
    _ = 516 ^ 6 * δ ^ (-12 * b) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast hδ.le]
      congr 2
      ring

/-- For a sufficiently small planiness error, the complete anchor palette
is bounded by an arbitrarily prescribed power loss. -/
theorem natural_packet_palette_parameters {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 ≤ b) (hbε : b ≤ ε / 48) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∃ A : ℕ, 1 ≤ A ∧ δ ^ (-b) ≤ A ∧
        (((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) ≤ δ ^ (-(ε / 2)) := by
  obtain ⟨d, hd, Hcut⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (by positivity : 0 < ε / 4) (by positivity : (0 : ℝ) < (516 ^ 6)⁻¹)
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right _ _, ?_⟩
  intro δ hδ hδd
  have hδ1 := hδd.trans (min_le_right _ _)
  obtain ⟨A, hA, hAd, hcard⟩ := natural_packet_palette_bound hδ hδ1 hb
  have hconst : 516 ^ 6 * δ ^ (ε / 4) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Hcut δ hδ (hδd.trans (min_le_left _ _)))
      (by positivity : (0 : ℝ) ≤ 516 ^ 6)
    norm_num at hh ⊢
    exact hh
  refine ⟨A, hA, hAd, hcard.trans ?_⟩
  calc
    _ = (516 ^ 6 * δ ^ (ε / 4)) * δ ^ (-12 * b - ε / 4) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ δ ^ (-12 * b - ε / 4) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hconst
        (Real.rpow_nonneg hδ.le (-12 * b - ε / 4))
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
