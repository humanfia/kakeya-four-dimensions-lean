-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters

open scoped BigOperators

lemma sqrt_le_mul_sqrts {F θ N k : ℝ} (hF : 1 ≤ F) (hθ : 0 ≤ θ) (hN : 0 ≤ N)
    (hk : k ≤ F * θ * N) :
    Real.sqrt k ≤ F * Real.sqrt θ * Real.sqrt N := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · calc
      k ≤ F * θ * N := hk
      _ ≤ F ^ 2 * θ * N := by
        gcongr
        nlinarith
      _ = (F * Real.sqrt θ * Real.sqrt N) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hθ, Real.sq_sqrt hN]

lemma fine_sum {J : ℕ} (k u : Fin J → ℝ) {P L F θ N V : ℝ}
    (hP : 0 ≤ P) (hF : 1 ≤ F) (hθ : 0 < θ) (hN : 0 < N)
    (hk0 : ∀ j, 0 ≤ k j) (hk : ∀ j, k j ≤ F * θ * N)
    (hu : ∀ j, P * Real.sqrt θ * Real.sqrt (k j) ≤ u j)
    (hmass : L * N ≤ ∑ j, k j) (hsum : ∑ j, u j ≤ V) :
    P * L / F * Real.sqrt N ≤ V := by
  have hF0 : 0 < F := lt_of_lt_of_le one_pos hF
  have hj : ∀ j, P * Real.sqrt θ * k j ≤
      (F * Real.sqrt θ * Real.sqrt N) * u j := by
    intro j
    calc
      P * Real.sqrt θ * k j =
          P * Real.sqrt θ * (Real.sqrt (k j) * Real.sqrt (k j)) := by
        rw [Real.mul_self_sqrt (hk0 j)]
      _ ≤ P * Real.sqrt θ *
          ((F * Real.sqrt θ * Real.sqrt N) * Real.sqrt (k j)) := by
        gcongr
        exact sqrt_le_mul_sqrts hF hθ.le hN.le (hk j)
      _ = (F * Real.sqrt θ * Real.sqrt N) *
          (P * Real.sqrt θ * Real.sqrt (k j)) := by ring
      _ ≤ (F * Real.sqrt θ * Real.sqrt N) * u j := by gcongr; exact hu j
  have hbig : P * Real.sqrt θ * (L * N) ≤
      (F * Real.sqrt θ * Real.sqrt N) * V := by
    calc
      P * Real.sqrt θ * (L * N) ≤ P * Real.sqrt θ * ∑ j, k j := by gcongr
      _ ≤ (F * Real.sqrt θ * Real.sqrt N) * ∑ j, u j := by
        simp only [Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _ => hj j)
      _ ≤ (F * Real.sqrt θ * Real.sqrt N) * V := by gcongr
  have hcancel : (Real.sqrt θ * Real.sqrt N) * (P * L * Real.sqrt N) ≤
      (Real.sqrt θ * Real.sqrt N) * (F * V) := by
    convert hbig using 1 <;> ring_nf
    rw [Real.sq_sqrt hN.le]
    ring
  have hh := le_of_mul_le_mul_left hcancel
    (mul_pos (Real.sqrt_pos.2 hθ) (Real.sqrt_pos.2 hN))
  have hh' : P * L * Real.sqrt N / F ≤ V :=
    (div_le_iff₀ hF0).mpr (by nlinarith only [hh])
  convert hh' using 1 <;> ring

lemma sqrt_scale_lower {R X : ℝ} (hR : 1 ≤ R) (hX : 0 ≤ X) (h : 1 ≤ R * X) :
    1 ≤ R * Real.sqrt X := by
  have hR0 : 0 ≤ R := by linarith
  have hs : 1 ≤ (R * Real.sqrt X) ^ 2 := by
    calc
      1 ≤ R * (R * X) := one_le_mul_of_one_le_of_one_le hR h
      _ = _ := by rw [mul_pow, Real.sq_sqrt hX]; ring
  nlinarith [mul_nonneg hR0 (Real.sqrt_nonneg X)]

lemma three_half {δ : ℝ} (hδ : 0 < δ) :
    δ ^ (3 / 2 : ℝ) = δ * Real.sqrt δ := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add_one hδ.ne']
  ring

lemma coarse_sum {J : ℕ} (k u : Fin J → ℝ) {L F s δ N V : ℝ}
    (hL : 0 ≤ L) (hF : 0 < F) (hs : 0 < s) (hδ : 0 < δ)
    (hk0 : ∀ j, 0 ≤ k j) (hk : ∀ j, k j * s ^ 2 ≤ F)
    (hu : ∀ j, L * δ ^ 2 ≤ u j)
    (hmass : L * N ≤ ∑ j, k j) (hsum : ∑ j, u j ≤ V) :
    L ^ 2 * N * δ ^ 2 * s ^ 2 ≤ F * V := by
  have hj : ∀ j, (L * δ ^ 2) * (k j * s ^ 2) ≤ F * u j := by
    intro j
    calc
      (L * δ ^ 2) * (k j * s ^ 2) ≤ (L * δ ^ 2) * F := by gcongr; exact hk j
      _ ≤ u j * F := by gcongr; exact hu j
      _ = _ := mul_comm _ _
  calc
    L ^ 2 * N * δ ^ 2 * s ^ 2 = (L * δ ^ 2 * s ^ 2) * (L * N) := by ring
    _ ≤ (L * δ ^ 2 * s ^ 2) * ∑ j, k j := by gcongr
    _ ≤ F * ∑ j, u j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      convert hj j using 1 <;> ring
    _ ≤ F * V := by gcongr

lemma coarse_target {δ m N L G s V : ℝ} (hδ : 0 < δ) (hm : 1 ≤ m)
    (hN : 0 < N) (hL : 0 ≤ L) (hG : 0 < G) (hs : 0 < s)
    (hslab : 1 ≤ 8 * m * N * δ)
    (hvol : L ^ 2 * N * δ ^ 2 * s ^ 2 ≤ (m * G) * V) :
    (s ^ 2 / (8 * G)) * (L ^ 2 / m ^ 2) * δ ^ (3 / 2 : ℝ) * Real.sqrt N ≤ V := by
  have hm0 : 0 < m := by linarith
  have hslab' : 1 ≤ (8 * m) * (N * δ) := by nlinarith
  have hroot := sqrt_scale_lower (show 1 ≤ 8 * m by linarith)
    (mul_pos hN hδ).le hslab'
  rw [Real.sqrt_mul hN.le δ] at hroot
  have hbase : δ ^ (3 / 2 : ℝ) * Real.sqrt N ≤ 8 * m * N * δ ^ 2 := by
    rw [three_half hδ]
    have h := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ δ * Real.sqrt δ * Real.sqrt N by positivity)
    convert h using 1 <;> ring_nf
    rw [Real.sq_sqrt hN.le, Real.sq_sqrt hδ.le]
    ring
  have hh : (L ^ 2 * s ^ 2) * (δ ^ (3 / 2 : ℝ) * Real.sqrt N) ≤
      (8 * G * m ^ 2) * V := by
    calc
      _ ≤ (L ^ 2 * s ^ 2) * (8 * m * N * δ ^ 2) := by gcongr
      _ = 8 * m * (L ^ 2 * N * δ ^ 2 * s ^ 2) := by ring
      _ ≤ 8 * m * ((m * G) * V) := by gcongr
      _ = _ := by ring
  apply le_of_mul_le_mul_left (a := 8 * G * m ^ 2) _ (by positivity)
  convert hh using 1 <;> field_simp <;> ring

lemma fine_powers {δ : ℝ} (hδ : 0 < δ) (C K q : ℝ) :
    δ ^ ((3 / 2 : ℝ) + q) * (δ ^ (C * q) * δ ^ q) ^ K * (δ ^ (-q)) ^ (-K) *
        (δ ^ (C * q) * δ ^ q) / δ ^ (-q) =
      δ ^ ((3 / 2 : ℝ) + ((K + 1) * C + (2 * K + 3)) * q) := by
  rw [← Real.rpow_add hδ, ← Real.rpow_mul hδ.le,
    ← Real.rpow_mul hδ.le, div_eq_mul_inv, ← Real.rpow_neg hδ.le]
  simp only [neg_neg, ← Real.rpow_add hδ]
  congr 1
  ring

lemma coarse_powers {δ : ℝ} (hδ : 0 < δ) (C q : ℝ) :
    ((δ ^ (C * q) * δ ^ q) ^ 2 / (δ ^ (-q)) ^ 2) * δ ^ (3 / 2 : ℝ) =
      δ ^ ((3 / 2 : ℝ) + (2 * C + 4) * q) := by
  rw [← Real.rpow_two (δ ^ (C * q) * δ ^ q), ← Real.rpow_two (δ ^ (-q)),
    ← Real.rpow_add hδ, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le,
    ← Real.rpow_sub hδ, ← Real.rpow_add hδ]
  congr 1
  ring

lemma target_identity {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) (a ε : ℝ) :
    a * δ ^ ε * (N * δ ^ 2) * (N * δ) ^ (-(1 / 2 : ℝ)) =
      a * δ ^ ((3 / 2 : ℝ) + ε) * Real.sqrt N := by
  rw [Real.mul_rpow hN.le hδ.le, ← Real.rpow_two δ, Real.sqrt_eq_rpow]
  have hNid : N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 / 2 : ℝ) := by
    nth_rw 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    norm_num
  have hδid : δ ^ ε * δ ^ (2 : ℝ) * δ ^ (-(1 / 2 : ℝ)) =
      δ ^ ((3 / 2 : ℝ) + ε) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = a * (δ ^ ε * δ ^ (2 : ℝ) * δ ^ (-(1 / 2 : ℝ))) *
        (N * N ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hNid, hδid]

lemma neg_rpow_ge_one {δ q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 ≤ q) :
    1 ≤ δ ^ (-q) := by
  simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -q ≤ 0 by linarith)

lemma choose_exponents {C K ε : ℝ} (hC : 1 ≤ C) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ((K + 1) * C + (2 * K + 3)) * q ≤ ε ∧ (2 * C + 4) * q ≤ ε := by
  let D := 10 * (C + 1) * (K + 1)
  have hC0 : 0 < C := by linarith
  have hK0 : 0 < K := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  let q := min (1 / 4 : ℝ) (ε / D)
  have hq : 0 < q := lt_min (by norm_num) (div_pos hε hD)
  have hqD : q * D ≤ ε := (le_div_iff₀ hD).mp (min_le_right _ _)
  have hCK : 0 ≤ C * K := mul_nonneg hC0.le hK0.le
  have hf : ((K + 1) * C + (2 * K + 3)) ≤ D := by dsimp [D]; nlinarith
  have hc : 2 * C + 4 ≤ D := by dsimp [D]; nlinarith
  refine ⟨q, hq, (min_le_left _ _).trans (by norm_num), ?_, ?_⟩
  · calc
      _ ≤ D * q := by gcongr
      _ ≤ ε := by nlinarith only [hqD]
  · calc
      _ ≤ D * q := by gcongr
      _ ≤ ε := by nlinarith only [hqD]

lemma compact_estimate {δ d q N V B ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 < d) (hdd : d ≤ δ) (hq : q ≤ 1) (hN : 1 ≤ N) (hB : 0 < B)
    (hε : 0 < ε) (hvol : δ ^ q * δ ^ 2 ≤ V)
    (hcount : N * δ ^ 2 ≤ δ ^ (-q) * B) :
    (d ^ 6 / B) * δ ^ ((3 / 2 : ℝ) + ε) * Real.sqrt N ≤ V := by
  have hN0 : 0 ≤ N := by linarith
  have hdq : δ ≤ δ ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hq
  have hmδ : δ ^ (-q) * δ ≤ 1 := by
    calc
      δ ^ (-q) * δ ≤ δ ^ (-q) * δ ^ q := by gcongr
      _ = 1 := by rw [← Real.rpow_add hδ]; simp
  have hNd : N * d ^ 3 ≤ B := by
    calc
      N * d ^ 3 ≤ N * δ ^ 3 := by gcongr
      _ = (N * δ ^ 2) * δ := by ring
      _ ≤ (δ ^ (-q) * B) * δ := by gcongr
      _ = B * (δ ^ (-q) * δ) := by ring
      _ ≤ B * 1 := by gcongr
      _ = B := mul_one _
  have hdV : d ^ 3 ≤ V := by
    calc
      d ^ 3 ≤ δ ^ 3 := by gcongr
      _ = δ * δ ^ 2 := by ring
      _ ≤ δ ^ q * δ ^ 2 := by gcongr
      _ ≤ V := hvol
  have hroot : Real.sqrt N ≤ N := Real.sqrt_le_iff.mpr ⟨hN0, by nlinarith⟩
  have hpow : δ ^ ((3 / 2 : ℝ) + ε) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1 (by linarith)
  calc
    (d ^ 6 / B) * δ ^ ((3 / 2 : ℝ) + ε) * Real.sqrt N ≤ (d ^ 6 / B) * 1 * N := by
      gcongr
    _ = (d ^ 3 / B) * (N * d ^ 3) := by ring
    _ ≤ (d ^ 3 / B) * B := by gcongr
    _ = d ^ 3 := div_mul_cancel₀ _ hB.ne'
    _ ≤ V := hdV

end WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters
