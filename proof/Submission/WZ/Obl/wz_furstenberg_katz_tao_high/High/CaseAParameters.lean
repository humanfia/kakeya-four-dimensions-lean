-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseABudget

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- Choose the regularity and profile errors before the palette length.
All coefficient conditions of Case A then hold at every admissible model
scale, using one common dyadic range for the pins. -/
theorem caseA_parameter_cutoff {s γ η : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hγ : 0 < γ) (hη : 0 < η) :
    ∃ ℓ d₀ ε' : ℝ, ∃ N₀ : ℕ,
      0 < ℓ ∧ ℓ ≤ 1 ∧ 0 < d₀ ∧ 0 < ε' ∧ ε' ≤ 1 ∧ 0 < N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 52 ∧
      ∀ (r ε₀ ε κ d : ℝ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
        (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
        (tb : ℕ → E2 × E2 → E2 × E2),
        HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb → r ≤ r₀ →
        0 ≤ ε₀ → ε₀ ≤ ε' → 0 ≤ ε → ε ≤ ε' → 0 ≤ κ → κ ≤ ε' →
        0 ≤ d → d ≤ d₀ →
        ∀ w δ : ℝ, r ≤ w → 26 * w ≤ 1 / 2 → 0 < δ → δ ≤ 1 → δ ≤ 2 * r ^ γ →
        r ≤ r ^ ℓ ∧ r ^ (-κ) * (r ^ ℓ) ^ (1 - s) ≤ 1 / 2 ∧
        ∃ KY : ℕ, ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY ∧
          max (max 27 (lineFrConst r s ε (r ^ ℓ)
            (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card d (palBase r n)))
            (winK0J r s ε d (winZ r s ε (r ^ ℓ)
              (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card w)) ≤ δ ^ (-η) ∧
          twoEndedConst r κ ε ≤ δ ^ (-η) ∧
          winC2 r s ε d (winZ r s ε (r ^ ℓ)
            (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card w) * 2 ^ s ≤
              δ ^ (-((1 - s) / 2)) := by
  let μ := min η ((1 - s) / 2)
  have hμ : 0 < μ := lt_min hη (by positivity)
  let τ := γ * μ / 1000
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let ℓ := min 1 τ
  have hℓ : 0 < ℓ := lt_min zero_lt_one hτ
  have hℓ1 : ℓ ≤ 1 := min_le_left _ _
  have hℓτ : ℓ ≤ τ := min_le_right _ _
  let ε' := min 1 (min τ (ℓ * (1 - s) / 2))
  have hε' : 0 < ε' := lt_min zero_lt_one (lt_min hτ (by positivity))
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'τ : ε' ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hε'ℓ : ε' ≤ ℓ * (1 - s) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * s / τ + 1)
  have hN₀pos : 0 < N₀ := by
    have hh : 0 ≤ 2 * s / τ := by positivity
    have hh' : (0 : ℝ) < N₀ := by linarith
    exact_mod_cast hh'
  obtain ⟨rP, hrP, _, hpin⟩ := fail_pinConst_small_power hτ
  have hC : 0 ≤ caseAPowerConst s := by linarith only [(caseAPowerConst_bounds s).1]
  obtain ⟨rT, hrT, _, htransfer⟩ := small_loss_transfer hγ hμ hC (D := 2) (by norm_num)
  obtain ⟨rF, hrF, hfar⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := ℓ * (1 - s) / 2) (B := 1 / 2) (by positivity) (by norm_num)
  refine ⟨ℓ, τ, ε', N₀, hℓ, hℓ1, hτ, hε', hε'1, hN₀pos, ?_⟩
  intro n hn
  have hnpos : 0 < n := hN₀pos.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlen : 2 * s / (n : ℝ) ≤ τ := by
    have hnn : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hh : 2 * s / τ ≤ (n : ℝ) := by linarith
    have hh' := (div_le_iff₀ hτ).mp hh
    rw [div_le_iff₀ hnR]
    linarith
  refine ⟨min rP (min rT (min rF (1 / 52))),
    lt_min hrP (lt_min hrT (lt_min hrF (by norm_num))),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro r ε₀ ε κ d P D S J₀ cls J₁ tb H hrr hε₀ hε₀' hε hεsmall hκ hκsmall hd hdsmall
    w δ hrw hw26 hδ hδ1 hδr
  have hr := H.fail.r_pos
  have hrP' := hrr.trans (min_le_left _ _)
  have hrT' := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrF' := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr52 : r ≤ 1 / 52 := hrr.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r < 1 := by linarith
  have hετ := hεsmall.trans hε'τ
  have hε₀τ := hε₀'.trans hε'τ
  have hκτ := hκsmall.trans hε'τ
  have hκℓ := hκsmall.trans hε'ℓ
  have hε1 := hεsmall.trans hε'1
  have hℓs : ℓ * s ≤ τ := by nlinarith only [hℓ.le, hℓτ, hs1.le]
  have hbudget : 30 * ε + ε₀ + ℓ * s + τ + 4 * d + 2 * s / n + κ ≤ γ * μ / 2 := by
    have he : γ * μ = 1000 * τ := by dsimp [τ]; ring
    rw [he]
    linarith only [hετ, hε₀τ, hℓs, hlen, hκτ, hdsmall, hτ]
  have hrℓ : r ≤ r ^ ℓ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1.le hℓ1
  have hfar' : r ^ (-κ) * (r ^ ℓ) ^ (1 - s) ≤ 1 / 2 := by
    rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
    exact (Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith only [hκℓ])).trans
      (hfar r hr hrF')
  obtain ⟨KY, hKY, hPC⟩ := hpin r s ε₀ ε (S.image Prod.fst) S H.failS hrP' hε1
  have hPCr := hPC r le_rfl (by linarith only [hr52])
  have hPCw := hPC w hrw hw26
  have hb := H.caseA_constants_le_power (ℓ := ℓ) (ν := τ) (d := d) hr1.le (by linarith only [hr52])
    hnpos hs0 hs1.le hε hε₀ hκ hℓ.le hτ.le hd (hr.trans_le hrw) (by linarith only [hw26]) hPCr hPCw
  have hfit := htransfer r δ (30 * ε + ε₀ + ℓ * s + τ + 4 * d + 2 * s / n + κ)
    hr hrT' hδ hδr hbudget
  have hηpow : δ ^ (-μ) ≤ δ ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_left _ _))
  have hepow : δ ^ (-μ) ≤ δ ^ (-((1 - s) / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_right _ _))
  exact ⟨hrℓ, hfar', KY, hKY, hb.1.trans (hfit.trans hηpow),
    hb.2.1.trans (hfit.trans hηpow), hb.2.2.trans (hfit.trans hepow)⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
