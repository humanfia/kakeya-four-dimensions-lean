-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.ClassSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Selecting a good class

`class_selection`: given nonnegative weights `w` on a finite index set `J` with total
`W > 0`, nonnegative counts `cl j k` (for `k ≤ L`) whose sums over `J` are bounded by `X k`,
and nonnegative `n2` with `ρ ∑ n2 ≤ W / 4`, some `j ∈ J` has positive weight,
`ρ n2 j ≤ w j`, and `cl j k ≤ 4 (L + 1) (w j / W) X k` for every `k ≤ L`.

Proof (Markov): bound every weight `w j` by `f j = ρ n2 j + ∑_{k ≤ L} W cl j k / (4 (L + 1) X k)`
(the terms with `X k ≤ 0` dropped) when `j` fails the conclusion; the sum of `f` over `J` is
at most `W / 4 + W / 4 = W / 2 < W`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem class_selection {ι : Type*} [DecidableEq ι] (J : Finset ι) (w n2 : ι → ℝ)
    (cl : ι → ℕ → ℝ) (X : ℕ → ℝ) (L : ℕ) {ρ W : ℝ}
    (hw : ∀ j ∈ J, 0 ≤ w j) (hcl : ∀ j ∈ J, ∀ k, 0 ≤ cl j k)
    (hW : W = ∑ j ∈ J, w j) (hWpos : 0 < W)
    (hX : ∀ k ≤ L, ∑ j ∈ J, cl j k ≤ X k)
    (hρ : 0 ≤ ρ) (hn2nn : ∀ j ∈ J, 0 ≤ n2 j) (hn2 : ρ * ∑ j ∈ J, n2 j ≤ W / 4) :
    ∃ j ∈ J, 0 < w j ∧ ρ * n2 j ≤ w j ∧
      ∀ k ≤ L, cl j k ≤ 4 * (L + 1) * (w j / W) * X k := by
  by_contra hcon
  push Not at hcon
  set a : ℝ := 4 * ((L : ℝ) + 1) with ha
  have ha_pos : 0 < a := by positivity
  set g : ι → ℕ → ℝ := fun j k => if 0 < X k then W * cl j k / (a * X k) else 0 with hg
  set f : ι → ℝ := fun j => ρ * n2 j + ∑ k ∈ Finset.range (L + 1), g j k with hf
  have hg_nn : ∀ j ∈ J, ∀ k, 0 ≤ g j k := by
    intro j hj k
    simp only [hg]
    split_ifs with h
    · exact div_nonneg (mul_nonneg hWpos.le (hcl j hj k)) (mul_nonneg ha_pos.le h.le)
    · exact le_refl 0
  have hgsum_nn : ∀ j ∈ J, 0 ≤ ∑ k ∈ Finset.range (L + 1), g j k :=
    fun j hj => Finset.sum_nonneg fun k _ => hg_nn j hj k
  have hf_nn : ∀ j ∈ J, 0 ≤ f j := fun j hj =>
    add_nonneg (mul_nonneg hρ (hn2nn j hj)) (hgsum_nn j hj)
  have hpt : ∀ j ∈ J, w j ≤ f j := by
    intro j hj
    rcases (hw j hj).eq_or_lt with h0 | hpos
    · rw [← h0]; exact hf_nn j hj
    · by_cases hn : ρ * n2 j ≤ w j
      · obtain ⟨k, hkL, hk⟩ := hcon j hj hpos hn
        have hXk : 0 < X k := by
          by_contra hXk
          push Not at hXk
          have hsum := hX k hkL
          have hle : cl j k ≤ ∑ i ∈ J, cl i k :=
            Finset.single_le_sum (fun i hi => hcl i hi k) hj
          have hnn : 0 ≤ ∑ i ∈ J, cl i k := Finset.sum_nonneg fun i hi => hcl i hi k
          have hX0 : X k = 0 := le_antisymm hXk (hnn.trans hsum)
          rw [hX0, mul_zero] at hk
          linarith
        have hwk : w j < g j k := by
          simp only [hg, ite_eq_left hXk]
          rw [lt_div_iff₀ (by positivity)]
          have hk' : a * (w j / W) * X k < cl j k := by rw [ha]; exact hk
          have e1 : a * (w j / W) * X k = w j * (a * X k) / W := by
            field_simp
          rw [e1, div_lt_iff₀ hWpos] at hk'
          linarith
        have hgk : g j k ≤ ∑ k' ∈ Finset.range (L + 1), g j k' :=
          Finset.single_le_sum (fun k' _ => hg_nn j hj k') (Finset.mem_range.mpr (by omega))
        have : 0 ≤ ρ * n2 j := mul_nonneg hρ (hn2nn j hj)
        simp only [hf]
        linarith
      · push Not at hn
        have := hgsum_nn j hj
        simp only [hf]
        linarith
  have hsum : ∑ j ∈ J, f j ≤ W / 2 := by
    have h1 : ∑ j ∈ J, f j =
        ρ * ∑ j ∈ J, n2 j + ∑ k ∈ Finset.range (L + 1), ∑ j ∈ J, g j k := by
      simp only [hf, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
    have h2 : ∀ k ∈ Finset.range (L + 1), ∑ j ∈ J, g j k ≤ W / a := by
      intro k hk
      have hkL : k ≤ L := by rw [Finset.mem_range] at hk; omega
      by_cases hXk : 0 < X k
      · simp only [hg, ite_eq_left hXk]
        rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff₀ (by positivity) ha_pos]
        have := hX k hkL
        have : W * (∑ i ∈ J, cl i k) ≤ W * X k := mul_le_mul_of_nonneg_left this hWpos.le
        nlinarith
      · simp only [hg, ite_eq_right hXk, Finset.sum_const_zero]
        positivity
    have h3 : ∑ k ∈ Finset.range (L + 1), ∑ j ∈ J, g j k ≤ ((L : ℝ) + 1) * (W / a) := by
      calc ∑ k ∈ Finset.range (L + 1), ∑ j ∈ J, g j k
          ≤ ∑ k ∈ Finset.range (L + 1), W / a := Finset.sum_le_sum h2
        _ = ((L : ℝ) + 1) * (W / a) := by simp
    have h4 : ((L : ℝ) + 1) * (W / a) = W / 4 := by
      rw [ha]; field_simp
    linarith
  have hle := Finset.sum_le_sum hpt
  rw [← hW] at hle
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
