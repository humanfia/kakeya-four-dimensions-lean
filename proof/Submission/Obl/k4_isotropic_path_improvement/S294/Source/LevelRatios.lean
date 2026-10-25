-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.LevelRatios, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Level ratios on the uniform grid (session x1088, for x1082's middle level).

* `exists_middle_level`: on the grid `s i = (i+1)/m`, between two levels separated by more than
  `X + Y + 1/m` there is a level at least `X` above the lower and `Y` below the upper one.
* `delta_ratio_le`: the path's depth tolerance turns a level gap into a thickness ratio,
  `δ(N, r_y)/δ(N, r_x) ≤ 2 N^-((s_y - s_x - 2 δ₀) L)`.
* `clock_ratio_le`: the path's clock bounds turn a level gap into a clock ratio,
  `2^-(T_y - T_x) ≤ N^-((κ₁ (s_y - s_x) - 2 δ₀) L)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Numerics

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- **A middle level.** -/
theorem exists_middle_level {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) {i ib : ℕ} {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hsep : X + Y + 1 / (m : ℝ) ≤ s ib - s i) :
    ∃ mid : ℕ, i ≤ mid ∧ mid ≤ ib ∧ X ≤ s mid - s i ∧ Y ≤ s ib - s mid := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set c := ⌈X * m⌉₊ with hc
  have hc_lo : X * m ≤ c := Nat.le_ceil _
  have hc_hi : (c : ℝ) < X * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdiff : ∀ a b : ℕ, s b - s a = ((b : ℝ) - a) / m := by
    intro a b; rw [hs, hs]; ring
  have hgap : X * m + Y * m + 1 ≤ (ib : ℝ) - i := by
    have := hsep
    rw [hdiff] at this
    rw [le_div_iff₀ hmR] at this
    have e : (X + Y + 1 / (m : ℝ)) * m = X * m + Y * m + 1 := by field_simp
    linarith
  have hle : i + c ≤ ib := by
    have : (i : ℝ) + c ≤ ib := by nlinarith
    exact_mod_cast this
  refine ⟨i + c, by omega, hle, ?_, ?_⟩
  · rw [hdiff, le_div_iff₀ hmR]; push_cast; linarith
  · rw [hdiff, le_div_iff₀ hmR]
    have hcast : ((ib : ℕ) : ℝ) - ((i + c : ℕ) : ℝ) = (ib : ℝ) - i - c := by
      push_cast; ring
    rw [hcast]
    nlinarith

/-- **Thickness ratio** from the depth tolerance. -/
theorem delta_ratio_le {N L δ₀ rx ry sx sy : ℝ} (hN : 1 < N) (hL : 0 ≤ L)
    (hrx : |rx - sx * L| ≤ δ₀ * L) (hry : |ry - sy * L| ≤ δ₀ * L) :
    O204.Split.δ N ry / O204.Split.δ N rx ≤ 2 * N ^ (-((sy - sx - 2 * δ₀) * L)) := by
  have hNp : 0 < N := by linarith
  have hlx : N ^ (-rx) ≤ O204.Split.δ N rx :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp rx).1
  have huy : O204.Split.δ N ry ≤ 2 * N ^ (-ry) :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp ry).2
  have hδx : 0 < O204.Split.δ N rx := O204.Tangent.δ_pos N rx
  rw [div_le_iff₀ hδx]
  have hrx' : rx ≤ (sx + δ₀) * L := by have := (abs_le.mp hrx).2; linarith
  have hry' : (sy - δ₀) * L ≤ ry := by have := (abs_le.mp hry).1; linarith
  calc O204.Split.δ N ry ≤ 2 * N ^ (-ry) := huy
    _ ≤ 2 * N ^ (-((sy - δ₀) * L)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
          (by norm_num)
    _ = 2 * N ^ (-((sy - sx - 2 * δ₀) * L)) * N ^ (-((sx + δ₀) * L)) := by
        rw [mul_assoc, ← Real.rpow_add hNp]; ring_nf
    _ ≤ 2 * N ^ (-((sy - sx - 2 * δ₀) * L)) * N ^ (-rx) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
          (by positivity)
    _ ≤ 2 * N ^ (-((sy - sx - 2 * δ₀) * L)) * O204.Split.δ N rx := by gcongr

/-- **Clock ratio** from the path's clock bounds. -/
theorem clock_ratio_le {N L κ₁ δ₀ sx sy : ℝ} {Tx Ty : ℕ} (hN : 1 < N) (hTxy : Tx ≤ Ty)
    (hTx : (2 : ℝ) ^ Tx ≤ N ^ ((κ₁ * sx + δ₀) * L))
    (hTy : N ^ ((κ₁ * sy - δ₀) * L) ≤ (2 : ℝ) ^ Ty) :
    ((2 : ℝ) ^ (Ty - Tx))⁻¹ ≤ N ^ (-((κ₁ * (sy - sx) - 2 * δ₀) * L)) := by
  have hNp : 0 < N := by linarith
  have hrel : ((2 : ℝ) ^ (Ty - Tx))⁻¹ = (2 : ℝ) ^ Tx / (2 : ℝ) ^ Ty := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num) hTxy]; field_simp
  rw [hrel, div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ Tx ≤ N ^ ((κ₁ * sx + δ₀) * L) := hTx
    _ = N ^ (-((κ₁ * (sy - sx) - 2 * δ₀) * L)) * N ^ ((κ₁ * sy - δ₀) * L) := by
        rw [← Real.rpow_add hNp]; ring_nf
    _ ≤ N ^ (-((κ₁ * (sy - sx) - 2 * δ₀) * L)) * (2 : ℝ) ^ Ty := by gcongr

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
