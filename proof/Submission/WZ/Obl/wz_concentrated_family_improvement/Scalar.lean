-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_family_improvement.Scalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_family_improvement.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_concentrated_family_improvement

/-- Weakening the coefficient and the gain weakens the requested bound. -/
theorem target_mono {σ w w' ε A A' δ m : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m)
    (hA : 0 ≤ A) (hAA : A ≤ A') (hw : w' ≤ w) :
    R σ w ε A δ m n ≤ R σ w' ε A' δ m n := by
  apply ENNReal.ofReal_le_ofReal
  have hp : δ ^ (w + ε) ≤ δ ^ (w' + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hAA hp (Real.rpow_nonneg hδ.le _) (hA.trans hAA))
        (inv_nonneg.mpr hm))
      (by positivity)) (Real.rpow_nonneg (by positivity) _)

/-- The exponent range makes the Katz--Tao parameter harmless on a fixed scale interval. -/
theorem core_bound {σ C d δ m : ℝ} {n : ℕ}
    (hσ : 0 ≤ σ) (hσtop : σ ≤ 1/2) (hC : 0 < C)
    (hd : 0 < d) (hdδ : d ≤ δ) (hδ1 : δ ≤ 1)
    (hm : 1 ≤ m) (hn : 0 < n) (hpack : (n : ℝ) * δ ^ 4 ≤ C) :
    m⁻¹ * (n * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ) ≤
      (C / d ^ 4) * d ^ (-σ) := by
  have hδ : 0 < δ := hd.trans_le hdδ
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd4 : 0 < d ^ 4 := pow_pos hd _
  have hnC : (n : ℝ) ≤ C / d ^ 4 := by
    apply (le_div_iff₀ hd4).2
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hd.le hdδ 4) hn0.le).trans hpack
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hnδ2 : (n : ℝ) * δ ^ 2 ≤ C / d ^ 4 :=
    (mul_le_of_le_one_right hn0.le hδ2).trans hnC
  have hnδ : d ≤ (n : ℝ) * δ :=
    hdδ.trans (le_mul_of_one_le_left hδ.le hn1)
  have hp : ((n : ℝ) * δ) ^ (-σ) ≤ d ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hd hnδ (neg_nonpos.mpr hσ)
  have hmexp : m ^ (-1 + (3/2 : ℝ) * σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)
  have hid : m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ) =
      m ^ (-1 + (3/2 : ℝ) * σ) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hm0.le _) (by positivity),
      ← Real.rpow_mul hm0.le]
    rw [show -(3/2 : ℝ) * -σ = (3/2 : ℝ) * σ by ring,
      Real.rpow_add hm0, Real.rpow_neg_one]
    ring
  rw [hid]
  calc
    m ^ (-1 + (3/2 : ℝ) * σ) * (n * δ ^ 2) * (n * δ) ^ (-σ)
        ≤ 1 * (n * δ ^ 2) * (n * δ) ^ (-σ) := by gcongr
    _ = (n * δ ^ 2) * (n * δ) ^ (-σ) := by ring
    _ ≤ (C / d ^ 4) * d ^ (-σ) :=
      mul_le_mul hnδ2 hp (by positivity) (by positivity)

/-- Packing and one dense tube suffice on any compact interval of scales. -/
theorem compact_coefficient {σ w ε ν C d : ℝ}
    (hσ : 0 ≤ σ) (hσtop : σ ≤ 1/2) (hwe : 0 ≤ w + ε)
    (hν : 0 ≤ ν) (hC : 0 < C) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ δ : ℝ, 0 < δ → d ≤ δ → δ ≤ 1 →
      ∀ m : ℝ, 1 ≤ m → ∀ n : ℕ, 0 < n → (n : ℝ) * δ ^ 4 ≤ C →
        R σ w ε A δ m n ≤ o (δ ^ ν * δ ^ 2) := by
  let M := (C / d ^ 4) * d ^ (-σ)
  have hM : 0 < M := by dsimp [M]; positivity
  let A := (d ^ ν * d ^ 2) / M
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro δ hδ hdδ hδ1 m hm n hn hpack
  apply ENNReal.ofReal_le_ofReal
  have hc := core_bound hσ hσtop hC hd hdδ hδ1 hm hn hpack
  have he : δ ^ (w + ε) ≤ 1 := Real.rpow_le_one hδ.le hδ1 hwe
  have hdens : d ^ ν * d ^ 2 ≤ δ ^ ν * δ ^ 2 :=
    mul_le_mul (Real.rpow_le_rpow hd.le hdδ hν)
      (pow_le_pow_left₀ hd.le hdδ 2) (by positivity) (by positivity)
  change A * δ ^ (w + ε) * m⁻¹ * (n * δ ^ 2) *
    (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ) ≤ δ ^ ν * δ ^ 2
  calc
    A * δ ^ (w + ε) * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ)
        = A * δ ^ (w + ε) *
          (m⁻¹ * (n * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ)) := by ring
    _ ≤ (A * 1) * M :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hA.le) hc
        (by have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm; positivity)
        (by positivity)
    _ = d ^ ν * d ^ 2 := by dsimp [A]; field_simp
    _ ≤ δ ^ ν * δ ^ 2 := hdens

end WangZahlLot.Obl.wz_concentrated_family_improvement
