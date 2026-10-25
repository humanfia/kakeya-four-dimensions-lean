-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.ScaleCases.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Arithmetic
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Counting

namespace WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters

open scoped BigOperators

lemma fine_estimate {J : ℕ} (k u : Fin J → ℝ) {δ θ C K q c N V ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hC : 1 ≤ C) (hq : 0 < q) (hc : 0 < c) (hN : 0 < N)
    (he : ((K + 1) * C + (2 * K + 3)) * q ≤ ε)
    (hk0 : ∀ j, 0 ≤ k j)
    (hk : ∀ j, k j ≤ (8 * C) * δ ^ (-q) * θ * N)
    (hu : ∀ j, c * δ ^ ((3 / 2 : ℝ) + q) * θ ^ ((1 / 2 : ℝ) - q) *
      (δ ^ (C * q) * δ ^ q) ^ K * (δ ^ (-q)) ^ (-K) * (k j) ^ (1 / 2 : ℝ) ≤ u j)
    (hmass : (δ ^ (C * q) * δ ^ q) * N ≤ ∑ j, k j) (hsum : ∑ j, u j ≤ V) :
    (c / (8 * C)) * δ ^ ((3 / 2 : ℝ) + ε) * Real.sqrt N ≤ V := by
  have hC0 : 0 < C := by linarith
  let L := δ ^ (C * q) * δ ^ q
  let m := δ ^ (-q)
  let P := c * δ ^ ((3 / 2 : ℝ) + q) * L ^ K * m ^ (-K)
  have hm : 1 ≤ m := neg_rpow_ge_one hδ hδ1 hq.le
  have hF : 1 ≤ (8 * C) * m := one_le_mul_of_one_le_of_one_le (by linarith) hm
  have hP : 0 ≤ P := by dsimp [P, L, m]; positivity
  have hlocal : ∀ j, P * Real.sqrt θ * Real.sqrt (k j) ≤ u j := by
    intro j
    have hkj := hk0 j
    have hθpow : θ ^ (1 / 2 : ℝ) ≤ θ ^ ((1 / 2 : ℝ) - q) :=
      Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by linarith)
    calc
      P * Real.sqrt θ * Real.sqrt (k j) =
          c * δ ^ ((3 / 2 : ℝ) + q) * θ ^ (1 / 2 : ℝ) *
            L ^ K * m ^ (-K) * (k j) ^ (1 / 2 : ℝ) := by
        dsimp [P]
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        ring
      _ ≤ c * δ ^ ((3 / 2 : ℝ) + q) * θ ^ ((1 / 2 : ℝ) - q) *
          L ^ K * m ^ (-K) * (k j) ^ (1 / 2 : ℝ) := by
        gcongr
      _ ≤ u j := hu j
  have hh := fine_sum k u hP hF hθ hN hk0 hk hlocal hmass hsum
  have hid : P * L / ((8 * C) * m) =
      (c / (8 * C)) * δ ^ ((3 / 2 : ℝ) + ((K + 1) * C + (2 * K + 3)) * q) := by
    rw [← fine_powers hδ C K q]
    dsimp [P, L, m]
    field_simp
  rw [hid] at hh
  have he' : δ ^ ((3 / 2 : ℝ) + ε) ≤
      δ ^ ((3 / 2 : ℝ) + ((K + 1) * C + (2 * K + 3)) * q) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he' (by positivity)) (Real.sqrt_nonneg N)).trans hh

lemma coarse_estimate {J : ℕ} (k u : Fin J → ℝ) {δ θ C q G s N V ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ) (hq : 0 < q)
    (hG : 0 < G) (hs : 0 < s) (hN : 0 < N) (hcoarse : s * θ ≤ δ)
    (he : (2 * C + 4) * q ≤ ε) (hk0 : ∀ j, 0 ≤ k j)
    (hk : ∀ j, k j * δ ^ 2 ≤ δ ^ (-q) * G * θ ^ 2)
    (hu : ∀ j, (δ ^ (C * q) * δ ^ q) * δ ^ 2 ≤ u j)
    (hmass : (δ ^ (C * q) * δ ^ q) * N ≤ ∑ j, k j)
    (hslab : 1 ≤ 8 * δ ^ (-q) * N * δ) (hsum : ∑ j, u j ≤ V) :
    (s ^ 2 / (8 * G)) * δ ^ ((3 / 2 : ℝ) + ε) * Real.sqrt N ≤ V := by
  let L := δ ^ (C * q) * δ ^ q
  let m := δ ^ (-q)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hm : 1 ≤ m := neg_rpow_ge_one hδ hδ1 hq.le
  have hm0 : 0 < m := by linarith
  have hk' : ∀ j, k j * s ^ 2 ≤ m * G := by
    intro j
    apply le_of_mul_le_mul_right (a := δ ^ 2) _ (sq_pos_of_pos hδ)
    calc
      k j * s ^ 2 * δ ^ 2 = (k j * δ ^ 2) * s ^ 2 := by ring
      _ ≤ (m * G * θ ^ 2) * s ^ 2 :=
        mul_le_mul_of_nonneg_right (hk j) (sq_nonneg s)
      _ = (m * G) * (s * θ) ^ 2 := by ring
      _ ≤ (m * G) * δ ^ 2 := by gcongr
  have hsum' := coarse_sum k u hL (mul_pos hm0 hG) hs hδ hk0 hk' hu hmass hsum
  have hh := coarse_target hδ hm hN hL hG hs hslab hsum'
  have hid : (s ^ 2 / (8 * G)) * (L ^ 2 / m ^ 2) * δ ^ (3 / 2 : ℝ) * Real.sqrt N =
      (s ^ 2 / (8 * G)) * δ ^ ((3 / 2 : ℝ) + (2 * C + 4) * q) * Real.sqrt N := by
    rw [← coarse_powers hδ C q]
    dsimp [L, m]
    ring
  rw [hid] at hh
  have he' : δ ^ ((3 / 2 : ℝ) + ε) ≤
      δ ^ ((3 / 2 : ℝ) + (2 * C + 4) * q) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he' (by positivity)) (Real.sqrt_nonneg N)).trans hh

end WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters
