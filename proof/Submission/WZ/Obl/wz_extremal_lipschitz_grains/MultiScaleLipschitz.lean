-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.MultiScaleLipschitz.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric

/-- **Multi-scale Lipschitz assembly** (sticky Lemma 4.7).  If on `E` the map `V` varies by at most
`r j` between points closer than `s j` (`j ≤ N`, `s` decreasing), is constant below `s N`, and is
bounded in variation by `2`, then it is `L`-Lipschitz on `E` whenever `L` dominates `r j / s (j+1)`
and `2 / s 0`. -/
theorem lipschitz_of_scales (V : Space → Space) (E : Set Space) (s r : ℕ → ℝ) (N : ℕ) (L : ℝ)
    (hs : ∀ j, 0 < s j) (hanti : ∀ j, s (j + 1) ≤ s j)
    (hscale : ∀ j < N, ∀ p ∈ E, ∀ q ∈ E, dist p q < s j → dist (V p) (V q) ≤ r j)
    (hfin : ∀ p ∈ E, ∀ q ∈ E, dist p q < s N → V p = V q)
    (hbig : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ 2)
    (hL0 : 2 ≤ L * s 0) (hLj : ∀ j < N, r j ≤ L * s (j + 1)) (hL : 0 ≤ L) :
    ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ L * dist p q := by
  intro p hp q hq
  set d := dist p q with hd
  by_cases hN : d < s N
  · rw [hfin p hp q hq hN, dist_self]; positivity
  push Not at hN
  by_cases h0 : s 0 ≤ d
  · calc dist (V p) (V q) ≤ 2 := hbig p hp q hq
      _ ≤ L * s 0 := hL0
      _ ≤ L * d := mul_le_mul_of_nonneg_left h0 hL
  push Not at h0
  -- find the scale bracket
  have hex : ∃ j, j < N ∧ s (j + 1) ≤ d ∧ d < s j := by
    classical
    have hP : ∃ j, s j ≤ d := ⟨N, hN⟩
    set j₀ := Nat.find hP with hj₀
    have hj₀s : s j₀ ≤ d := Nat.find_spec hP
    have hj₀pos : j₀ ≠ 0 := by
      intro h; rw [h] at hj₀s; linarith
    have hj₀N : j₀ ≤ N := Nat.find_min' hP hN
    refine ⟨j₀ - 1, by omega, ?_, ?_⟩
    · rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj₀pos)]
    · have := Nat.find_min hP (show j₀ - 1 < j₀ by omega)
      push Not at this
      exact this
  obtain ⟨j, hjN, hj1, hj2⟩ := hex
  calc dist (V p) (V q) ≤ r j := hscale j hjN p hp q hq hj2
    _ ≤ L * s (j + 1) := hLj j hjN
    _ ≤ L * d := mul_le_mul_of_nonneg_left hj1 hL

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
