-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.TubeBounds

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

noncomputable section

lemma polynomial_coefficient_bound {C δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hCd : C * δ ≤ 1) (hn : (n : ℝ) * δ ^ 4 ≤ C) :
    (n : ℝ) / δ ≤ δ ^ (-(6 : ℝ)) := by
  rw [Real.rpow_neg hδ.le, Real.rpow_ofNat]
  apply (mul_le_mul_iff_left₀ (pow_pos hδ 6)).mp
  rw [inv_mul_cancel₀ (pow_ne_zero 6 hδ.ne')]
  have he : (n : ℝ) / δ * δ ^ 6 = (n : ℝ) * δ ^ 4 * δ := by field_simp
  rw [he]
  exact (mul_le_mul_of_nonneg_right hn hδ.le).trans hCd

/-- All fixed losses fit into the requested exponent once the scale is small enough. -/
theorem choose_parameters (C ν : ℝ) (hC : 0 < C) (hν : 0 < ν) :
    let ε := ν / 20
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / 2 ∧ C * δ ≤ 1 ∧
      (δ ^ ε) ^ p * δ ^ (-(6 : ℝ)) ≤ 1 ∧
      2 ≤ δ * (δ ^ (-ε)) ^ p ∧
      δ ^ ν * (4 * (p + 1 : ℝ) ^ 2) ≤ δ ^ ε ∧
      128 * (1024 * (2 : ℝ) ^ p * (δ ^ (-ε)) ^ 2) ^ 2 ≤ δ ^ (-ν) := by
  dsimp only
  let ε := ν / 20
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hνε : ν = 20 * ε := by dsimp [ε]; ring
  obtain ⟨p, hp⟩ := exists_nat_gt (6 / ε)
  have hpε : 6 < ε * p := by
    have := (div_lt_iff₀ hε).mp hp
    nlinarith
  have hp0 : 0 < p := by
    by_contra hh
    have : p = 0 := by omega
    norm_num [this] at hpε
  let M : ℝ := 1024 * (2 : ℝ) ^ p
  let A : ℝ := max (128 * M ^ 2) (4 * (p + 1 : ℝ) ^ 2)
  have hM : 0 < M := by dsimp [M]; positivity
  have hA : 0 < A := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let d₁ : ℝ := A ^ (-(1 : ℝ) / ε)
  have hd₁ : 0 < d₁ := Real.rpow_pos_of_pos hA _
  have hd₁pow : d₁ ^ ε = A⁻¹ := by
    dsimp [d₁]
    rw [← Real.rpow_mul hA.le]
    have he : (-(1 : ℝ) / ε) * ε = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
  refine ⟨p, min (1 / 2) (min (1 / (C + 1)) d₁), hp0,
    lt_min (by norm_num) (lt_min (by positivity) hd₁), ?_⟩
  intro δ hδ hδd
  have hδhalf : δ ≤ 1 / 2 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδC : δ ≤ 1 / (C + 1) := (hδd.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδD : δ ≤ d₁ := (hδd.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsmall : A * δ ^ ε ≤ 1 := calc
    A * δ ^ ε ≤ A * d₁ ^ ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδD hε.le) hA.le
    _ = 1 := by rw [hd₁pow, mul_inv_cancel₀ hA.ne']
  have hCd : C * δ ≤ 1 := calc
    C * δ ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left hδC hC.le
    _ ≤ 1 := by rw [← div_eq_mul_one_div]; exact (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨hδhalf, hCd, ?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
    exact Real.rpow_le_one hδ.le hδ1 (by change 0 ≤ ε * (p : ℝ) + -6; linarith)
  · have hinv : 2 ≤ δ⁻¹ := by
      apply (mul_le_mul_iff_left₀ hδ).mp
      rw [inv_mul_cancel₀ hδ.ne']
      linarith
    calc
      2 ≤ δ⁻¹ := hinv
      _ = δ ^ (-(1 : ℝ)) := (Real.rpow_neg_one δ).symm
      _ ≤ δ ^ (1 - ε * p) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ ((1 : ℝ) + (-ε * p)) := by congr 1; ring
      _ = δ ^ (1 : ℝ) * δ ^ (-ε * p) := Real.rpow_add hδ _ _
      _ = δ * (δ ^ (-ε)) ^ p := by rw [Real.rpow_one, Real.rpow_mul_natCast hδ.le]
  · have hpow : δ ^ (ν - ε) ≤ δ ^ ε :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hconst : 4 * (p + 1 : ℝ) ^ 2 ≤ A := le_max_right _ _
    have hh : δ ^ (ν - ε) * (4 * (p + 1 : ℝ) ^ 2) ≤ 1 := calc
      δ ^ (ν - ε) * (4 * (p + 1 : ℝ) ^ 2) ≤ δ ^ ε * A :=
        mul_le_mul hpow hconst (by positivity) (by positivity)
      _ ≤ 1 := by simpa only [mul_comm] using hsmall
    have he : δ ^ ν = δ ^ ε * δ ^ (ν - ε) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le ε)]
  · have hpow : δ ^ (ν - 4 * ε) ≤ δ ^ ε :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hconst : 128 * M ^ 2 ≤ A := le_max_left _ _
    have hh : (128 * M ^ 2) * δ ^ (ν - 4 * ε) ≤ 1 :=
      (mul_le_mul hconst hpow (by positivity) hA.le).trans hsmall
    have he : (δ ^ (-ε)) ^ 4 * δ ^ ν = δ ^ (ν - 4 * ε) := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
      congr 1
      ring
    have hproduct : 128 * (M * (δ ^ (-ε)) ^ 2) ^ 2 * δ ^ ν ≤ 1 := calc
      128 * (M * (δ ^ (-ε)) ^ 2) ^ 2 * δ ^ ν = 128 * M ^ 2 * ((δ ^ (-ε)) ^ 4 * δ ^ ν) := by ring
      _ ≤ 1 := by rw [he]; exact hh
    rw [Real.rpow_neg hδ.le ν]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hδ ν)).mp
    rw [inv_mul_cancel₀ (Real.rpow_pos_of_pos hδ ν).ne']
    exact hproduct

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
