-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.GridMono, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Depths and clocks increase along the levels (session x1088).

With the grid `s i = (i+1)/m` and the tolerance `4 δ₀ m ≤ κ₁ ≤ 1` (`exists_relative_grid`,
hypothesis of `SampleProducer`/`StagesProducer`), the path bounds
`|r i - s i L| ≤ δ₀ L` and `N^((κ₁ s i - δ₀) L) ≤ 2^(T i) ≤ N^((κ₁ s i + δ₀) L)` make the depths
`r` strictly increasing and the clocks `T` increasing on all levels `< m`, so the thicknesses
`δ(N, r i)` decrease:
* `r_lt_of_grid`, `r_le_of_grid`, `T_le_of_grid`, `delta_le_of_r_le`, `delta_le_of_grid`;
* `PathData.Valid` forms: `path_r_le`, `path_T_le`, `path_delta_le`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Numerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- **Depths increase strictly.** -/
theorem r_lt_of_grid {L κ₁ δ₀ : ℝ} {m : ℕ} {s r : ℕ → ℝ} (hL : 0 < L) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hκ1 : κ₁ ≤ 1)
    (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L) {i j : ℕ} (hij : i < j) (hj : j < m) :
    r i < r j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hri := (abs_le.mp (hr i (by omega))).2
  have hrj := (abs_le.mp (hr j hj)).1
  have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  have hsd : 1 / (m : ℝ) ≤ s j - s i := by
    rw [hs, hs, div_sub_div_same, div_le_div_iff_of_pos_right hmR]; linarith
  have hδ : 2 * δ₀ < 1 / (m : ℝ) := by
    rw [lt_div_iff₀ hmR]; nlinarith
  have : (2 * δ₀) * L < (s j - s i) * L := mul_lt_mul_of_pos_right (by linarith) hL
  nlinarith

/-- **Depths increase.** -/
theorem r_le_of_grid {L κ₁ δ₀ : ℝ} {m : ℕ} {s r : ℕ → ℝ} (hL : 0 < L) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hκ1 : κ₁ ≤ 1)
    (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L) {i j : ℕ} (hij : i ≤ j) (hj : j < m) :
    r i ≤ r j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact (r_lt_of_grid hL hm hs hδm hκ1 hr h hj).le
  · have : i = j := le_antisymm hij h
    rw [this]

/-- **Clocks increase.** -/
theorem T_le_of_grid {N L κ₁ δ₀ : ℝ} {m : ℕ} {s : ℕ → ℝ} {T : ℕ → ℕ} (hN : 1 < N) (hL : 0 < L)
    (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    (hκ : 0 < κ₁)
    (hT : ∀ i, i < m → N ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i ∧
      (2 : ℝ) ^ T i ≤ N ^ ((κ₁ * s i + δ₀) * L)) {i j : ℕ} (hij : i ≤ j) (hj : j < m) :
    T i ≤ T j := by
  rcases Nat.lt_or_ge i j with h | h
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
    have hsd : 1 / (m : ℝ) ≤ s j - s i := by
      rw [hs, hs, div_sub_div_same, div_le_div_iff_of_pos_right hmR]; linarith
    have hδ : 2 * δ₀ ≤ κ₁ * (1 / (m : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hmR]; nlinarith
    have hsep : κ₁ * s i + δ₀ ≤ κ₁ * s j - δ₀ := by nlinarith
    exact clock_mono hN hL.le (hT i (by omega)).2 (hT j hj).1 hsep
  · have : i = j := le_antisymm hij h
    rw [this]

/-- **Thicknesses decrease** with the depth. -/
theorem delta_le_of_r_le {N r r' : ℝ} (hN : 1 ≤ N) (hrr : r ≤ r') :
    O204.Split.δ N r' ≤ O204.Split.δ N r := by
  unfold O204.Split.δ
  apply zpow_le_zpow_right₀ (by norm_num)
  apply neg_le_neg
  apply Int.floor_le_floor
  have hlog : 0 ≤ Real.log N / Real.log 2 :=
    div_nonneg (Real.log_nonneg hN) (Real.log_pos (by norm_num)).le
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hrr hlog

/-- **Thicknesses decrease** along the levels. -/
theorem delta_le_of_grid {N L κ₁ δ₀ : ℝ} {m : ℕ} {s r : ℕ → ℝ} (hN : 1 ≤ N) (hL : 0 < L)
    (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    (hκ1 : κ₁ ≤ 1) (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L) {i j : ℕ} (hij : i ≤ j)
    (hj : j < m) : O204.Split.δ N (r j) ≤ O204.Split.δ N (r i) :=
  delta_le_of_r_le hN (r_le_of_grid hL hm hs hδm hκ1 hr hij hj)

section Path

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}

/-- The path's depths increase along the levels. -/
theorem path_r_le (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hL : 0 < L) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hκ1 : κ₁ ≤ 1)
    {i j : ℕ} (hij : i ≤ j) (hj : j < m) : p.r i ≤ p.r j :=
  r_le_of_grid hL hm hs hδm hκ1 (fun l hl => (hp.2.2.2.2.1 l hl).1) hij hj

/-- The path's clocks increase along the levels. -/
theorem path_T_le (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 < Nk) (hL : 0 < L)
    (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    (hκ : 0 < κ₁) {i j : ℕ} (hij : i ≤ j) (hj : j < m) : p.T i ≤ p.T j :=
  T_le_of_grid hN hL hm hs hδm hκ
    (fun l hl => ⟨(hp.2.2.2.2.1 l hl).2.2.1, (hp.2.2.2.2.1 l hl).2.2.2.1⟩) hij hj

/-- The path's thicknesses decrease along the levels. -/
theorem path_delta_le (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk) (hL : 0 < L)
    (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    (hκ1 : κ₁ ≤ 1) {i j : ℕ} (hij : i ≤ j) (hj : j < m) :
    O204.Split.δ Nk (p.r j) ≤ O204.Split.δ Nk (p.r i) :=
  delta_le_of_r_le hN (path_r_le hp hL hm hs hδm hκ1 hij hj)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
