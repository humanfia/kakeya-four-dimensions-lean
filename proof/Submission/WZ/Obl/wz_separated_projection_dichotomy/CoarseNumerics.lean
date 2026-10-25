-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.DyadicDepth
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerBudget

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- Dyadic mass regularization has arbitrarily small power cost. -/
theorem exists_coarse_scale_budget {ℓ α ζ R : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hα1 : α ≤ 1) (hζ : 0 < ζ) (hR : 0 ≤ R)
    (hαℓ : α ≤ ℓ / 100) (hαζ : α ≤ ℓ * ζ / 100) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ n : ℕ,
        dyadicRadius (n + 1) < δ ^ (α + 2) / (6 * (2 * R + 1) ^ 2) ∧
        2 * δ ^ (-ℓ / 4) * (4 * ((n + 1 : ℕ) : ℝ) ^ 3 / δ ^ α) ≤ δ ^ (-ℓ) ∧
        (4 * ((n + 1 : ℕ) : ℝ) ^ 3 / δ ^ α) * (2 * δ ^ (-ℓ / 4)) ^ ζ ≤ (δ ^ (-ℓ)) ^ ζ ∧
        δ ^ (3 * α) ≤ δ ^ α / (16 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
  obtain ⟨dN, hdN, hdN1, hN⟩ := exists_dyadic_depth_budget (p := α / 12) (by positivity)
  obtain ⟨dA, hdA, hdA1, hA⟩ := exists_monomial_bound (6 * (2 * R + 1) ^ 2)
    (a := 4) (b := α + 2) (by linarith)
  obtain ⟨dC, hdC, hdC1, hC⟩ := exists_monomial_bound (8 : ℝ)
    (a := -ℓ / 4 - 2 * α) (b := -ℓ) (by linarith)
  obtain ⟨dL, hdL, hdL1, hL⟩ := exists_monomial_bound (4 * (2 : ℝ) ^ ζ)
    (a := -2 * α + (-ℓ / 4) * ζ) (b := (-ℓ) * ζ) (by nlinarith)
  obtain ⟨dD, hdD, hdD1, hD⟩ := exists_monomial_bound (16 : ℝ)
    (a := 2 * α) (b := α) (by linarith)
  refine ⟨min dN (min dA (min dC (min dL dD))), by positivity,
    (min_le_left _ _).trans hdN1, ?_⟩
  intro δ hδ hsmall
  have hsN := hsmall.trans (min_le_left _ _)
  have hsA := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsC := ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsL := (((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hsD := (((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hsN.trans hdN1
  have hpow4 : δ ^ (4 : ℕ) ≤ δ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ (4 : ℕ) by norm_num)
  obtain ⟨n, hnlow, hnlast, hn⟩ := hN (δ ^ (4 : ℕ)) (by positivity) (hpow4.trans hsN)
  have hident : (δ ^ (4 : ℕ)) ^ (α / 12) = δ ^ (α / 3) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    congr 1
    ring
  rw [hident] at hn
  have hn3 : ((n + 1 : ℕ) : ℝ) ^ 3 * δ ^ α ≤ 1 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ) * δ ^ (α / 3)) hn 3
    rw [mul_pow, ← Real.rpow_mul_natCast hδ.le] at hp
    norm_num only [Nat.cast_ofNat, one_pow] at hp
    simpa only [show α / 3 * (3 : ℝ) = α by ring] using hp
  have hnc : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ δ ^ (-α) := by
    rw [Real.rpow_neg hδ.le, inv_eq_one_div]
    exact (le_div_iff₀ (by positivity : 0 < δ ^ α)).mpr hn3
  have hLc : 4 * ((n + 1 : ℕ) : ℝ) ^ 3 / δ ^ α ≤ 4 * δ ^ (-2 * α) := by
    calc _ ≤ 4 * δ ^ (-α) / δ ^ α := by gcongr
      _ = 4 * δ ^ (-2 * α) := by
        rw [mul_div_assoc, ← Real.rpow_sub hδ]
        congr 2
        ring
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · apply hnlast.trans_le
    apply (le_div_iff₀ (by positivity : 0 < 6 * (2 * R + 1) ^ 2)).mpr
    have ha := hA δ hδ hsA
    simp only [Real.rpow_ofNat] at ha
    nlinarith
  · calc _ ≤ 2 * δ ^ (-ℓ / 4) * (4 * δ ^ (-2 * α)) := by gcongr
      _ = 8 * δ ^ (-ℓ / 4 - 2 * α) := by
        rw [sub_eq_add_neg, Real.rpow_add hδ]
        ring
      _ ≤ _ := hC δ hδ hsC
  · calc _ ≤ (4 * δ ^ (-2 * α)) * (2 * δ ^ (-ℓ / 4)) ^ ζ := by gcongr
      _ = (4 * (2 : ℝ) ^ ζ) * δ ^ (-2 * α + (-ℓ / 4) * ζ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le, Real.rpow_add hδ]
        ring
      _ ≤ δ ^ ((-ℓ) * ζ) := hL δ hδ hsL
      _ = _ := Real.rpow_mul hδ.le _ _
  · apply (le_div_iff₀ (by positivity : 0 < 16 * ((n + 1 : ℕ) : ℝ) ^ 3)).mpr
    calc δ ^ (3 * α) * (16 * ((n + 1 : ℕ) : ℝ) ^ 3) ≤ δ ^ (3 * α) * (16 * δ ^ (-α)) := by gcongr
      _ = 16 * δ ^ (2 * α) := by
        rw [show δ ^ (3 * α) * (16 * δ ^ (-α)) = 16 * (δ ^ (3 * α) * δ ^ (-α)) by ring,
          ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ δ ^ α := hD δ hδ hsD

end WangZahlLot.Obl.wz_separated_projection_dichotomy
