-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormNumerics

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

/-- Choose the fine error and cutoff after fixing the output error and scale net. -/
theorem normalization_parameters {β ε dmax : ℝ}
    (hβ : 0 < β) (hβ4 : β ≤ 1 / 4) (hε : 0 < ε) (hmax : 0 < dmax) :
    ∃ (η : ℝ) (L : ℕ) (d0 : ℝ), 0 < η ∧ 0 < L ∧ 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d0 →
        NormBounds η β δ (3 * δ ^ (-η)) dmax L ∧
        (3 * δ ^ (-η) * δ) ^ ε ≤ (3 * δ ^ (-η) * δ) ^ (ε / 2) / 2 ∧
        32 * δ ^ (-η) ≤ (3 * δ ^ (-η) * δ) ^ (-ε) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / β)
  let L := N + 1
  have hL : 0 < L := Nat.succ_pos _
  have hgrid : 1 ≤ β / 2 * ((L - 1 : ℕ) : ℝ) := by
    dsimp [L]
    have hh := (div_lt_iff₀ hβ).mp hN
    nlinarith only [hh]
  let η : ℝ := min (β / (100 * ((L : ℝ) + 3))) (min (ε / 100) (1 / 100))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hη100 : η ≤ 1 / 100 := (min_le_right _ _).trans (min_le_right _ _)
  have hηε : 4 * η ≤ ε := by
    have hh : η ≤ ε / 100 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hh, hη.le]
  have hbudget : (22 + 9 * (L : ℝ)) * η ≤ β / 2 := by
    have hh : η ≤ β / (100 * ((L : ℝ) + 3)) := min_le_left _ _
    have hh' := (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * ((L : ℝ) + 3))).mp hh
    nlinarith only [hh', hη.le, mul_nonneg (Nat.cast_nonneg L) hη.le]
  obtain ⟨dC, hdC, hC⟩ := exists_rpow_cutoff hη
    (by positivity : (0 : ℝ) < 1 / (10 ^ 60 * ((L + 1 : ℕ) : ℝ)))
  obtain ⟨dS, hdS, hS⟩ := exists_rpow_cutoff (by norm_num : (0 : ℝ) < 1 / 2)
    (lt_min hmax (by norm_num : (0 : ℝ) < 1 / 10 ^ 12))
  refine ⟨η, L, min dC dS, hη, hL, lt_min hdC hdS, ?_⟩
  intro δ hδ hδ1 hδd
  have hsmall := norm_constant_bound hδ (hC δ hδ (hδd.trans (min_le_left _ _)))
  have hb := norm_numerics hδ hδ1 hη hη100 hβ hβ4 hbudget hgrid hsmall
    (hS δ hδ (hδd.trans (min_le_right _ _)))
  have h32 : 32 ≤ δ ^ (-η) := by
    have hL1 : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
    have : (32 : ℝ) ≤ 10 ^ 60 * ((L + 1 : ℕ) : ℝ) := by nlinarith only [hL1]
    exact this.trans hsmall
  exact ⟨hb, norm_output_bounds hδ hδ1 (by positivity) hb.half_scale hε hηε h32⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
