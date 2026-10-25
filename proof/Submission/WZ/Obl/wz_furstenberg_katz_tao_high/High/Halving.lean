-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Halving.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/Halving.lean (b19b589).
import Mathlib

/-!
# Halving scale selection for the point profile

A scalar lemma on a palette of scales. Index `i` stands for the scale `r ^ (i / N)`, and `G i`
is the (base `r⁻¹`, times `N`) exponent of the number of occupied cells of the pin set at that
scale. So `G` has slope at most `2` (a cell splits into at most `≈ 4 ^ k` subcells) and,
for a normalized one-dimensional pin set, `G i ≥ i` up to the error `E`.

At the level `n` (resolution `r ^ (n / N)`), case A needs a cell scale `h ∈ [n/2, n - w]` that is a
right-minimum of `φ i = G i - s i` on `[h, n]`: then the cells are relatively `s`-Frostman
down to the resolution (Kaufman's full heights). If the minimum of `φ` on `[n/2, n]` is only
attained within `w` of `n`, the exponent excess `G - id` at `n/2` exceeds the one at `n` by
about `(1 - s) n/2`. Iterating `n ↦ n/2` from `N = 2 ^ K M` down to `M`, the excess would grow
beyond the trivial bound `G M ≤ 2 M`. So some level has a case-A window.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

/-- **One halving step.** If no `h ∈ [m, 2m - w]` is a right-minimum of `G i - s i` on `[h, 2m]`,
then `G m ≥ G (2m) - s m - (2 - s) w - E`. -/
theorem halving_step (G : ℕ → ℝ) {m w : ℕ} {s E : ℝ} (hs : s ≤ 2)
    (hlip : ∀ i j, i ≤ j → G j - G i ≤ 2 * ((j : ℝ) - i) + E)
    (hnot : ¬ ∃ h, m ≤ h ∧ h + w ≤ 2 * m ∧
      ∀ i, h ≤ i → i ≤ 2 * m → G h - s * h ≤ G i - s * i) :
    G (2 * m) - s * m - (2 - s) * w - E ≤ G m := by
  obtain ⟨h, hhS, hmin⟩ := (Finset.Icc m (2 * m)).exists_min_image
    (fun i => G i - s * i) ⟨m, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hmh : m ≤ h := (Finset.mem_Icc.mp hhS).1
  have hh2 : h ≤ 2 * m := (Finset.mem_Icc.mp hhS).2
  have hclose : 2 * m < h + w := by
    by_contra hle
    exact hnot ⟨h, hmh, by omega, fun i hi hi2 =>
      hmin i (Finset.mem_Icc.mpr ⟨le_trans hmh hi, hi2⟩)⟩
  have hm := hmin m (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hl := hlip h (2 * m) hh2
  have hcast : ((2 * m : ℕ) : ℝ) < (h : ℝ) + w := by exact_mod_cast hclose
  push_cast at hl hcast
  nlinarith

/-- **Halving selection.** Levels `n_j = 2 ^ j M`, `j ≤ K`, with margins `w (j + 1)` at the level
`n_(j+1)`. If the margins and the error are small against `(1 - s) n_j / 2` and `K` is large
enough, some level `n_(j+1)` (`j < K`) has a case-A window: a cell scale
`h ∈ [n_j, n_(j+1) - w (j+1)]` with `G h - s h ≤ G i - s i` for every `i ∈ [h, n_(j+1)]`. -/
theorem halving_select (G : ℕ → ℝ) {K M : ℕ} {s E : ℝ} (hs1 : s < 1)
    (w : ℕ → ℕ)
    (hlip : ∀ i j, i ≤ j → G j - G i ≤ 2 * ((j : ℝ) - i) + E)
    (htop : ((2 ^ K * M : ℕ) : ℝ) - E ≤ G (2 ^ K * M))
    (hbot : G M ≤ 2 * M + E)
    (hw : ∀ j, (2 - s) * (w (j + 1) : ℝ) + E ≤ (1 - s) / 2 * ((2 ^ j * M : ℕ) : ℝ))
    (hK : (M : ℝ) + 2 * E < (1 - s) / 2 * ((2 ^ K - 1 : ℕ) * M : ℝ)) :
    ∃ j, j < K ∧ ∃ h, 2 ^ j * M ≤ h ∧ h + w (j + 1) ≤ 2 ^ (j + 1) * M ∧
      ∀ i, h ≤ i → i ≤ 2 ^ (j + 1) * M → G h - s * h ≤ G i - s * i := by
  by_contra hno
  push Not at hno
  -- the excess `u j = G (n_j) - n_j` grows by `(1 - s) n_j / 2` at each halving
  have hstep : ∀ j, j < K →
      G (2 ^ (j + 1) * M) - ((2 ^ (j + 1) * M : ℕ) : ℝ) + (1 - s) / 2 * ((2 ^ j * M : ℕ) : ℝ) ≤
        G (2 ^ j * M) - ((2 ^ j * M : ℕ) : ℝ) := by
    intro j hj
    have hnot : ¬ ∃ h, 2 ^ j * M ≤ h ∧ h + w (j + 1) ≤ 2 * (2 ^ j * M) ∧
        ∀ i, h ≤ i → i ≤ 2 * (2 ^ j * M) → G h - s * h ≤ G i - s * i := by
      rintro ⟨h, h1, h2, h3⟩
      obtain ⟨i, hi1, hi2, hi3⟩ := hno j hj h h1 (by rw [pow_succ]; linarith)
      exact (not_le.mpr hi3) (h3 i hi1 (by rw [pow_succ] at hi2; linarith))
    have h1 := halving_step G (m := 2 ^ j * M) (w := w (j + 1)) (by linarith) hlip hnot
    have h2 := hw j
    have he : 2 ^ (j + 1) * M = 2 * (2 ^ j * M) := by ring
    rw [he]
    push_cast at h1 h2 ⊢
    nlinarith
  -- sum the steps from the top level `K` down to `0`
  have hsum : ∀ k, k ≤ K →
      G (2 ^ K * M) - ((2 ^ K * M : ℕ) : ℝ) +
          (1 - s) / 2 * (((2 ^ K - 2 ^ (K - k) : ℕ) : ℝ) * M) ≤
        G (2 ^ (K - k) * M) - ((2 ^ (K - k) * M : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ K := by omega
      have hih := ih hk'
      have hj : K - (k + 1) < K := by omega
      have hs := hstep (K - (k + 1)) hj
      have hidx : K - (k + 1) + 1 = K - k := by omega
      rw [hidx] at hs
      have hle1 : 2 ^ (K - (k + 1)) ≤ 2 ^ (K - k) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle2 : 2 ^ (K - k) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpow : (2 : ℕ) ^ (K - k) = 2 * 2 ^ (K - (k + 1)) := by
        rw [← pow_succ']; congr 1; omega
      have hc1 : ((2 ^ K - 2 ^ (K - (k + 1)) : ℕ) : ℝ) =
          ((2 ^ K - 2 ^ (K - k) : ℕ) : ℝ) + ((2 ^ (K - (k + 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (le_trans hle1 hle2), Nat.cast_sub hle2, hpow]
        push_cast; ring
      rw [hc1]
      push_cast at hs hih ⊢
      nlinarith
  have hfin := hsum K le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at hfin
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
