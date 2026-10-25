-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.Budgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ScaleBudget
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LightArithmetic

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

/-- Absorb a fixed coefficient using a strictly positive exponent gap. -/
lemma exists_power_absorption {C p r : ℝ} (hC : 0 < C) (hgap : r < p) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * δ ^ p ≤ δ ^ r := by
  obtain ⟨d, hd, hb⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hgap) (inv_pos.mpr hC)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have hh : C * δ ^ (p - r) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (hb δ hδ hδd) hC.le
    simpa only [mul_inv_cancel₀ hC.ne'] using hm
  calc
    C * δ ^ p = (C * δ ^ (p - r)) * δ ^ r := by
      rw [mul_assoc, ← Real.rpow_add hδ, sub_add_cancel]
    _ ≤ 1 * δ ^ r := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := one_mul _

/-- All numerical requirements of the coarse-class assembly, at one fine scale. -/
structure ComparisonBudget (δ ε κ η s v t P ηC dC : ℝ) (q : ℕ) : Prop where
  small : δ < 1 / 208
  root : 2080000 * δ ^ ((1 - ε ^ 2) * (2 - s) - η - (1 + ε ^ 2)) < 1
  residual : (112 * (6 * 81 ^ 3)) * δ ^ (ε ^ 2) ≤ δ ^ η
  light : lightMassConstant q * δ ^ (ε ^ 3 / 4 - 3 * v - 3 * t) ≤ 1
  ratio : 26 * δ ^ (ε ^ 2 / 2) ≤ 1
  size : ∀ n : ℕ, (n : ℝ) * δ ^ 6 ≤ P → 2 * (n : ℝ) < (δ ^ (-v)) ^ q
  level : ∀ L : ℕ, δ ≤ ((2 : ℝ) ^ L)⁻¹ →
    4 * (L + 1 : ℝ) * δ ^ t ≤ δ ^ η ∧ 4 * (L + 1 : ℝ) * δ ^ κ ≤ δ ^ η
  relative : ∀ τ : ℝ, 0 < τ → τ ≤ δ ^ (ε ^ 2 / 2) →
    τ ≤ dC ∧ τ ≤ 1 / 100 ∧ 54 ≤ τ ^ (-ηC)

/-- Fix the number of weight bins and every scale cutoff before seeing the tube family. -/
theorem exists_comparison_budget {ε κ η s v t P ηC dC : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hv : 0 < v) (hP : 0 < P)
    (hηC : 0 < ηC) (hdC : 0 < dC)
    (hroot : 0 < (1 - ε ^ 2) * (2 - s) - η - (1 + ε ^ 2))
    (hres : η < ε ^ 2) (hlight : 0 < ε ^ 3 / 4 - 3 * v - 3 * t)
    (hremove : 3 * η < t) (hretain : 3 * η < κ) :
    ∃ q : ℕ, 0 < q ∧ ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ComparisonBudget δ ε κ η s v t P ηC dC q := by
  obtain ⟨q, hq⟩ := exists_nat_gt (7 / v)
  have hvq : 7 < v * q := by have hh := (div_lt_iff₀ hv).mp hq; nlinarith
  have hqpos : 0 < q := by
    by_contra hh
    have he : q = 0 := by omega
    norm_num [he] at hvq
  have hr : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨dR, hdR, hbR⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hroot (by norm_num : (0 : ℝ) < 1 / 4160000)
  obtain ⟨dE, hdE, hbE⟩ := exists_power_absorption
    (by norm_num : (0 : ℝ) < 112 * (6 * 81 ^ 3)) hres
  obtain ⟨dB, hdB, hbB⟩ := exists_power_absorption
    (show 0 < lightMassConstant q by unfold lightMassConstant; positivity) hlight
  obtain ⟨dS, hdS, hbS⟩ := exists_power_absorption (by norm_num : (0 : ℝ) < 26) hr
  obtain ⟨dI, hdI, hbI⟩ := exists_dyadic_index_cutoff hη
  obtain ⟨dM, hdM, hbM⟩ := exists_power_absorption (by norm_num : (0 : ℝ) < 4)
    (show η < t - 2 * η by linarith)
  obtain ⟨dK, hdK, hbK⟩ := exists_power_absorption (by norm_num : (0 : ℝ) < 4)
    (show η < κ - 2 * η by linarith)
  obtain ⟨dC', hdC', hbC'⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hr (lt_min hdC (by norm_num : (0 : ℝ) < 1 / 100))
  obtain ⟨dT, hdT, hbT⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (mul_pos hr hηC) (by norm_num : (0 : ℝ) < 1 / 54)
  obtain ⟨dP, hdP, hbP⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (by norm_num : (0 : ℝ) < 1) (show 0 < 1 / (4 * P) by positivity)
  let d := min (1 / 416) (min dR (min dE (min dB (min dS (min dI
    (min dM (min dK (min dC' (min dT dP)))))))))
  refine ⟨q, hqpos, d, by dsimp [d]; positivity, ?_⟩
  intro δ hδ hd
  simp only [d, le_min_iff] at hd
  obtain ⟨hdsmall, hdR', hdE', hdB', hdS', hdI', hdM', hdK', hdC'', hdT', hdP'⟩ := hd
  have hδ1 : δ ≤ 1 := by linarith
  refine ⟨by linarith, ?_, hbE δ hδ hdE', ?_, ?_, ?_, ?_, ?_⟩
  · have hh := hbR δ hδ hdR'
    linarith
  · simpa only [Real.rpow_zero] using hbB δ hδ hdB'
  · simpa only [Real.rpow_zero] using hbS δ hδ hdS'
  · intro n hn
    have hPd : 4 * P * δ ≤ 1 := by
      have hh := hbP δ hδ hdP'
      rw [Real.rpow_one] at hh
      simpa only [mul_comm δ] using (le_div_iff₀ (by positivity : 0 < 4 * P)).mp hh
    have hsize : 2 * (n : ℝ) * δ ^ (7 : ℝ) < 1 := by
      have hh := mul_le_mul_of_nonneg_right hn hδ.le
      rw [Real.rpow_ofNat]
      nlinarith
    have hpow : 2 * (n : ℝ) < δ ^ (-7 : ℝ) := by
      rw [Real.rpow_neg hδ.le, ← one_div]
      exact (lt_div_iff₀ (by positivity : 0 < δ ^ (7 : ℝ))).mpr hsize
    calc
      2 * (n : ℝ) < δ ^ (-7 : ℝ) := hpow
      _ ≤ δ ^ (-v * q) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
      _ = (δ ^ (-v)) ^ q := Real.rpow_mul_natCast hδ.le _ _
  · intro L hL
    have hindex := hbI δ hδ hδ1 hdI' L hL
    constructor
    · calc
        4 * (L + 1 : ℝ) * δ ^ t ≤ 4 * δ ^ (-2 * η) * δ ^ t := by gcongr
        _ = 4 * δ ^ (t - 2 * η) := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
        _ ≤ _ := hbM δ hδ hdM'
    · calc
        4 * (L + 1 : ℝ) * δ ^ κ ≤ 4 * δ ^ (-2 * η) * δ ^ κ := by gcongr
        _ = 4 * δ ^ (κ - 2 * η) := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
        _ ≤ _ := hbK δ hδ hdK'
  · intro τ hτ hτδ
    have hh := hτδ.trans (hbC' δ hδ hdC'')
    refine ⟨hh.trans (min_le_left _ _), hh.trans (min_le_right _ _), ?_⟩
    have hp : τ ^ ηC ≤ 1 / 54 := by
      calc
        τ ^ ηC ≤ (δ ^ (ε ^ 2 / 2)) ^ ηC := Real.rpow_le_rpow hτ.le hτδ hηC.le
        _ = δ ^ (ε ^ 2 / 2 * ηC) := (Real.rpow_mul hδ.le _ _).symm
        _ ≤ _ := hbT δ hδ hdT'
    rw [Real.rpow_neg hτ.le]
    have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 54)
      (Real.rpow_pos_of_pos hτ ηC)).mpr hp
    norm_num at hi
    exact hi

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
