import Submission.Obl.k4_scalar_profile_raw_certification.Extraction
import Submission.Lib.K4ModelReduction.PowerComparison

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter

/-- A narrow width has a fixed limiting exponent along a subsequence. The
exponent keeps both the narrowness gap and the original lower-width bound. -/
theorem narrow_exponent_subsequence (N H β : ℕ → ℝ) (c A e : ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (hc : 0 ≤ c) (hA : c ≤ A) (he : 0 < e)
    (hlow : ∀ k, N k ^ (-A) / H k ≤ β k)
    (hnarrow : ∃ᶠ k in atTop, N k ^ e * β k < N k ^ (-c)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ B : ℝ, c + e ≤ B ∧ B ≤ A ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        N (φ k) ^ (-B - δ) ≤ β (φ k) ∧ β (φ k) ≤ N (φ k) ^ (-B + δ) := by
  obtain ⟨θ, hθ, hθgood⟩ := extraction_of_frequently_atTop
    (hnarrow.and_eventually (hsub 1 zero_lt_one))
  have hpos : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hgt : ∀ k, 1 < N k := fun k => by linarith [hN k]
  have hHpos : ∀ k, 0 < H k := fun k => lt_of_lt_of_le zero_lt_one (hH k)
  have hsmall : ∀ k, β (θ k) ≤ N (θ k) ^ (-c - e) := by
    intro k
    have h := (hθgood k).1
    have hpow := Real.rpow_pos_of_pos (hpos (θ k)) e
    calc β (θ k) ≤ N (θ k) ^ (-c) / N (θ k) ^ e := by
          apply le_of_lt
          apply (lt_div_iff₀ hpow).mpr
          simpa only [mul_comm] using h
      _ = N (θ k) ^ (-c - e) := (Real.rpow_sub (hpos (θ k)) _ _).symm
  have henv : ∀ k, N (θ k) ^ (-(A + 1)) ≤ β (θ k) ∧
      β (θ k) ≤ N (θ k) ^ (A + 1) := by
    intro k
    have hHθ : H (θ k) ≤ N (θ k) := by simpa using (hθgood k).2
    constructor
    · calc N (θ k) ^ (-(A + 1)) = N (θ k) ^ (-A) / N (θ k) := by
            rw [show -(A + 1) = -A - 1 by ring,
              Real.rpow_sub (hpos (θ k)), Real.rpow_one]
        _ ≤ N (θ k) ^ (-A) / H (θ k) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (hpos _).le _) (hHpos _) hHθ
        _ ≤ β (θ k) := hlow _
    · exact (hsmall k).trans ((Real.rpow_le_one_of_one_le_of_nonpos
        (hgt _).le (by linarith)).trans (Real.one_le_rpow (hgt _).le (by linarith)))
  obtain ⟨ψ, hψ, C, hC⟩ :=
    Submission.Obl.k4_scalar_profile_raw_certification.exists_subseq_exponent
      (N ∘ θ) (β ∘ θ) (A + 1) (fun k => hN _) henv
  let φ : ℕ → ℕ := θ ∘ ψ
  let B : ℝ := -C
  have hφ : StrictMono φ := hθ.comp hψ
  have hfit : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      N (φ k) ^ (-B - δ) ≤ β (φ k) ∧ β (φ k) ≤ N (φ k) ^ (-B + δ) := by
    intro δ hδ
    simpa only [φ, B, neg_neg, Function.comp_apply] using hC δ hδ
  have hBmin : c + e ≤ B := by
    by_contra hn
    have hδ : 0 < (c + e - B) / 2 := by linarith
    obtain ⟨k, hk⟩ := (hfit _ hδ).exists
    have hcmp := hk.1.trans (hsmall (ψ k))
    have hcmp' := (Real.rpow_le_rpow_left_iff (hgt (φ k))).mp hcmp
    linarith
  have hBmax : B ≤ A := by
    by_contra hn
    have hδ : 0 < (B - A) / 2 := by linarith
    have hbound : -A ≤ -B + (B - A) / 2 :=
      Submission.Lib.K4ModelReduction.exponent_le_of_subpower_loss
        (N ∘ φ) (H ∘ φ) (hNt.comp hφ.tendsto_atTop)
        (fun ε hε => hφ.tendsto_atTop.eventually (hsub ε hε)) (by
          filter_upwards [hfit _ hδ] with k hk
          calc N (φ k) ^ (-A) ≤ H (φ k) * β (φ k) := by
                have h := hlow (φ k)
                exact (div_le_iff₀ (hHpos _)).mp h |>.trans_eq (mul_comm _ _)
            _ ≤ H (φ k) * N (φ k) ^ (-B + (B - A) / 2) :=
              mul_le_mul_of_nonneg_left hk.2 (hHpos _).le)
    linarith
  exact ⟨φ, hφ, B, hBmin, hBmax, hfit⟩

/-- The narrow exponent lies strictly between the transverse and full spatial
exponents at a true depth larger than the projected depth. -/
theorem exists_true_depth {κ ℓ s B : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hs : 0 < s) (hB : ℓ * s < B) :
    ∃ r : ℝ, s < r ∧ ℓ * r < B ∧ B < (κ + ℓ) * r ∧ r < B / ℓ := by
  have hBl : s < B / ℓ := (lt_div_iff₀ hℓ).mpr (by linarith)
  have hBpos : 0 < B := (mul_pos hℓ hs).trans hB
  have hkl : 0 < κ + ℓ := by linarith
  have hfrac : B / (κ + ℓ) < B / ℓ := div_lt_div_of_pos_left hBpos hℓ (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between (max_lt hBl hfrac)
  refine ⟨r, (le_max_left _ _).trans_lt hrlo, ?_, ?_, hrhi⟩
  · nlinarith [(lt_div_iff₀ hℓ).mp hrhi]
  · nlinarith [(div_lt_iff₀ hkl).mp ((le_max_right _ _).trans_lt hrlo)]

end Submission.Obl.k4_narrow_projected_row_parents
