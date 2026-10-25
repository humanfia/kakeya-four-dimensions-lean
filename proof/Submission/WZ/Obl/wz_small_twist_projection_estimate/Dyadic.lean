-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Dyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Dyadic summation

A finite family of lengths `Z j ≤ min (2, 2κ / |B j|)` whose members with `|B j| ≤ r` number at
most `D (κ + 2r + 4δ)` has total length `O((K + 1) D δ)` when all `|B j| ≤ 2^K δ`: split the
indices into the dyadic shells `2^(k-1) δ < |B j| ≤ 2^k δ`.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Finset

/-- The weight of index `j` in shell `k`. -/
private noncomputable def shellTerm (P : Prop) [Decidable P] (κ δ : ℝ) (k : ℕ) : ℝ :=
  if P then 4 * κ / (2 ^ k * δ) else 0

/-- Pointwise domination of a length by its dyadic shell weights. -/
private lemma le_sum_shell {Zj Bj δ κ : ℝ} {P : Prop} [Decidable P] (hδ : 0 < δ) (hκ : δ ≤ κ)
    (K : ℕ) (hZ0 : 0 ≤ Zj) (hZ2 : Zj ≤ 2) (hZB : Bj ≠ 0 → Zj * |Bj| ≤ 2 * κ)
    (hZP : ¬ P → Zj = 0) (hBK : |Bj| ≤ 2 ^ K * δ) :
    Zj ≤ ∑ k ∈ range (K + 1),
      (if P ∧ |Bj| ≤ 2 ^ k * δ then 4 * κ / (2 ^ k * δ) else 0) := by
  classical
  have hnonneg : ∀ k ∈ range (K + 1),
      0 ≤ (if P ∧ |Bj| ≤ 2 ^ k * δ then 4 * κ / (2 ^ k * δ) else (0 : ℝ)) := by
    intro k _
    split_ifs
    · have hκ0 : 0 < κ := hδ.trans_le hκ
      positivity
    · exact le_rfl
  by_cases hP : P
  swap
  · rw [hZP hP]
    exact sum_nonneg hnonneg
  have hex : ∃ k, |Bj| ≤ 2 ^ k * δ := ⟨K, hBK⟩
  set m := Nat.find hex with hm
  have hmspec : |Bj| ≤ 2 ^ m * δ := Nat.find_spec hex
  have hmK : m ≤ K := Nat.find_min' hex hBK
  have hterm : (if P ∧ |Bj| ≤ 2 ^ m * δ then 4 * κ / (2 ^ m * δ) else (0 : ℝ)) =
      4 * κ / (2 ^ m * δ) := by
    split_ifs with h
    · rfl
    · exact absurd ⟨hP, hmspec⟩ h
  have hZm : Zj ≤ 4 * κ / (2 ^ m * δ) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, one_mul, le_div_iff₀ hδ]
      nlinarith [mul_le_mul_of_nonneg_right hZ2 hδ.le]
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hlt : ¬ |Bj| ≤ 2 ^ m' * δ := Nat.find_min hex (by omega)
      push Not at hlt
      have hpos' : 0 < 2 ^ m' * δ := by positivity
      have hB0 : 0 < |Bj| := hpos'.trans hlt
      have hB : Bj ≠ 0 := abs_pos.mp hB0
      have h1 := hZB hB
      rw [hm', pow_succ, le_div_iff₀ (by positivity)]
      have h2 : Zj * (2 ^ m' * δ) ≤ Zj * |Bj| := mul_le_mul_of_nonneg_left hlt.le hZ0
      nlinarith
  calc Zj ≤ 4 * κ / (2 ^ m * δ) := hZm
    _ = (if P ∧ |Bj| ≤ 2 ^ m * δ then 4 * κ / (2 ^ m * δ) else (0 : ℝ)) := hterm.symm
    _ ≤ ∑ k ∈ range (K + 1),
          (if P ∧ |Bj| ≤ 2 ^ k * δ then 4 * κ / (2 ^ k * δ) else 0) :=
        single_le_sum hnonneg (mem_range.mpr (by omega))

/-- Dyadic summation of lengths. -/
lemma dyadic_sum_le {ι : Type*} (s : Finset ι) (Z B : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {δ κ D : ℝ} (hδ : 0 < δ) (hκ : δ ≤ κ) (hD : 0 ≤ D) (K : ℕ)
    (hZ0 : ∀ j ∈ s, 0 ≤ Z j) (hZ2 : ∀ j ∈ s, Z j ≤ 2)
    (hZB : ∀ j ∈ s, B j ≠ 0 → Z j * |B j| ≤ 2 * κ)
    (hZP : ∀ j ∈ s, ¬ P j → Z j = 0)
    (hBK : ∀ j ∈ s, |B j| ≤ 2 ^ K * δ)
    (hcount : ∀ k : ℕ, ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * δ)).card : ℝ) ≤
      D * (κ + 2 * (2 ^ k * δ) + 4 * δ)) :
    ∑ j ∈ s, Z j ≤ (K + 1) * (D * (4 * κ * (κ + 4 * δ) / δ + 8 * κ)) := by
  classical
  have hκ0 : 0 < κ := hδ.trans_le hκ
  calc ∑ j ∈ s, Z j
      ≤ ∑ j ∈ s, ∑ k ∈ range (K + 1),
          (if P j ∧ |B j| ≤ 2 ^ k * δ then 4 * κ / (2 ^ k * δ) else 0) := by
        refine sum_le_sum fun j hj => ?_
        exact le_sum_shell hδ hκ K (hZ0 j hj) (hZ2 j hj) (hZB j hj) (hZP j hj) (hBK j hj)
    _ = ∑ k ∈ range (K + 1), ∑ j ∈ s,
          (if P j ∧ |B j| ≤ 2 ^ k * δ then 4 * κ / (2 ^ k * δ) else 0) := sum_comm
    _ = ∑ k ∈ range (K + 1),
          ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * δ)).card : ℝ) * (4 * κ / (2 ^ k * δ)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (K + 1), D * (4 * κ * (κ + 4 * δ) / δ + 8 * κ) := by
        refine sum_le_sum fun k _ => ?_
        have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have hpos : 0 < 2 ^ k * δ := by positivity
        calc ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * δ)).card : ℝ) * (4 * κ / (2 ^ k * δ))
            ≤ D * (κ + 2 * (2 ^ k * δ) + 4 * δ) * (4 * κ / (2 ^ k * δ)) :=
              mul_le_mul_of_nonneg_right (hcount k) (by positivity)
          _ = D * (4 * κ * (κ + 4 * δ) / (2 ^ k * δ) + 8 * κ) := by
              field_simp
              ring
          _ ≤ D * (4 * κ * (κ + 4 * δ) / δ + 8 * κ) := by
              apply mul_le_mul_of_nonneg_left _ hD
              apply add_le_add_left
              apply div_le_div_of_nonneg_left (by positivity) hδ
              nlinarith
    _ = (K + 1) * (D * (4 * κ * (κ + 4 * δ) / δ + 8 * κ)) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

end WangZahlLot.Obl.wz_small_twist_projection_estimate
