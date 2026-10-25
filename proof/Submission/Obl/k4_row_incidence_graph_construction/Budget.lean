import Submission.Obl.k4_row_incidence_graph_construction.Loss

namespace Submission.Obl.k4_row_incidence_graph_construction

/-- A common subpower bound absorbs every polynomial loss of finite assembly. -/
theorem lossBounds_of_common_bound {K R s U L : ℝ}
    (hK : 1 ≤ K) (hKR : K ≤ R) (hRU : R ≤ U) (hU : 2 ≤ U) (hs : 0 ≤ s)
    (hL : (2 : ℝ) ^ 30 * U ^ (30 + 6 * s) ≤ L) : LossBounds K R s L := by
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hKU : K ≤ U := hKR.trans hRU
  have hp (n : ℕ) : K ^ n ≤ U ^ n := pow_le_pow_left₀ hK0 hKU n
  have hq (n : ℕ) : R ^ n ≤ U ^ n := pow_le_pow_left₀ hR0 hRU n
  have hn (n : ℕ) : 1 ≤ U ^ n := one_le_pow₀ hU1
  have hb {c : ℝ} {n : ℕ} (hc0 : 0 ≤ c) (hc : c ≤ (2 : ℝ) ^ 30)
      (hn' : (n : ℝ) ≤ 30 + 6 * s) : c * U ^ n ≤ L := by
    apply le_trans _ hL
    apply mul_le_mul hc _ (by positivity) (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hU1 hn'
  have hb' {n : ℕ} (hn' : (n : ℝ) ≤ 30 + 6 * s) : U ^ n ≤ L := by
    simpa using hb (c := 1) (by norm_num) (by norm_num) hn'
  have hcell : 6 * R ^ 2 + 2 ≤ 8 * U ^ 2 := by
    nlinarith [hq 2, hn 2]
  have hsum : 10 + 6 * R ^ 3 ≤ 16 * U ^ 3 := by
    nlinarith [hq 3, hn 3]
  have hden0 : 0 ≤ graphDenominator K R := by
    dsimp [graphDenominator]
    positivity
  have hden : graphDenominator K R ≤ (2 : ℝ) ^ 23 * U ^ 19 := by
    calc
      graphDenominator K R = 2048 * K ^ 11 * (6 * R ^ 2 + 2) ^ 4 := rfl
      _ ≤ 2048 * U ^ 11 * (8 * U ^ 2) ^ 4 := by gcongr
      _ = (2 : ℝ) ^ 23 * U ^ 19 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hKU.trans (by simpa using hb' (n := 1) (by norm_num only [Nat.cast_ofNat]; linarith))
  · exact (hq 3).trans (hb' (by norm_num only [Nat.cast_ofNat]; linarith))
  · calc
      K + K ^ 2 + 1 ≤ 3 * U ^ 2 := by
        have hUle : U ≤ U ^ 2 := by nlinarith
        nlinarith [hp 2, hn 2]
      _ ≤ L := hb (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)
  · calc
      K * graphDenominator K R ≤ U * ((2 : ℝ) ^ 23 * U ^ 19) := by
        exact mul_le_mul hKU hden hden0 hU0.le
      _ = (2 : ℝ) ^ 23 * U ^ 20 := by ring
      _ ≤ L := hb (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)
  · calc
      K * (10 + 6 * R ^ 3) ^ 2 ≤ U * (16 * U ^ 3) ^ 2 := by gcongr
      _ = 256 * U ^ 7 := by ring
      _ ≤ L := hb (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)
  · calc
      (6 * R ^ 2 + 2) ^ 2 * K * graphDenominator K R ≤
          (8 * U ^ 2) ^ 2 * U * ((2 : ℝ) ^ 23 * U ^ 19) := by
        gcongr
      _ = (2 : ℝ) ^ 29 * U ^ 24 := by ring
      _ ≤ L := hb (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)
  · have hrpow : (R ^ 6) ^ s ≤ U ^ (6 * s) := by
      calc
        (R ^ 6) ^ s ≤ (U ^ 6) ^ s := Real.rpow_le_rpow (by positivity) (hq 6) hs
        _ = U ^ (6 * s) := by simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast_mul hU0.le 6 s).symm
    calc
      512 * K ^ 10 * (R ^ 6) ^ s ≤ 512 * U ^ 10 * U ^ (6 * s) := by gcongr
      _ = 512 * U ^ (10 + 6 * s) := by
        rw [Real.rpow_add hU0, Real.rpow_ofNat]
        ring
      _ ≤ (2 : ℝ) ^ 30 * U ^ (30 + 6 * s) := by
        apply mul_le_mul (by norm_num) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
      _ ≤ L := hL
  · exact (mul_le_mul_of_nonneg_left (hp 5) (by norm_num : (0 : ℝ) ≤ 8)).trans
      (hb (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith))
  · calc
      2 + K ≤ 3 * U := by linarith
      _ ≤ L := by simpa using hb (n := 1) (c := 3) (by norm_num) (by norm_num) (by norm_num only [Nat.cast_ofNat]; linarith)

/-- Choose the arbitrary subpower requested from regularization. -/
theorem subpower_parameters (s a θ : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hθ : 0 < θ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ K R : ℝ, 1 ≤ K → K ≤ R → R ≤ N ^ ε →
        LossBounds K R s ((N ^ (-a)) ^ (-θ)) := by
  let b : ℝ := a * θ / 2
  let d : ℝ := 30 + 6 * s
  let ε : ℝ := b / d
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := by dsimp [d]; linarith
  have hε : 0 < ε := div_pos hb hd
  let N₀ : ℝ := max 2 (max ((2 : ℝ) ^ ε⁻¹) (((2 : ℝ) ^ 30) ^ b⁻¹))
  refine ⟨ε, hε, N₀, le_max_left _ _, ?_⟩
  intro N hN K R hK hKR hRN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by linarith
  have hNε : (2 : ℝ) ^ ε⁻¹ ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : ((2 : ℝ) ^ 30) ^ b⁻¹ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hU : 2 ≤ N ^ ε := by
    calc
      (2 : ℝ) = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
        (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
      _ ≤ N ^ ε := Real.rpow_le_rpow (by positivity) hNε hε.le
  have hC : (2 : ℝ) ^ 30 ≤ N ^ b := by
    calc
      (2 : ℝ) ^ 30 = (((2 : ℝ) ^ 30) ^ b⁻¹) ^ b :=
        (Real.rpow_inv_rpow (by positivity) hb.ne').symm
      _ ≤ N ^ b := Real.rpow_le_rpow (by positivity) hNb hb.le
  have hpower : (N ^ ε) ^ d = N ^ b := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    exact div_mul_cancel₀ b hd.ne'
  apply lossBounds_of_common_bound hK hKR hRN hU hs
  calc
    (2 : ℝ) ^ 30 * (N ^ ε) ^ (30 + 6 * s) = (2 : ℝ) ^ 30 * N ^ b := by
      rw [show 30 + 6 * s = d from rfl, hpower]
    _ ≤ N ^ b * N ^ b := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = N ^ (a * θ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      dsimp [b]
      ring
    _ = (N ^ (-a)) ^ (-θ) := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      ring

end Submission.Obl.k4_row_incidence_graph_construction
