-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ConfinementPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

def confinementConstant : ℝ :=
  (400000 * 4 * 16000) ^ 2 * (400000 * 16000) ^ 2 *
    (52428800000000 * (257 ^ 4 : ℕ))

lemma confinementConstant_pos : 0 < confinementConstant := by unfold confinementConstant; positivity

lemma confinementDensity_formula {a ρ c D s : ℝ} (ha : 0 < a) (hac : a ≤ ρ * c) :
    confinementDensity a ρ c D s = D ^ 4 /
      (confinementConstant * ((Scale.dyExp 1 (s / 2) : ℝ) + 1) ^ 2 *
        (1 + Real.log (2 * ρ * c / a))) := by
  have hratio : 1 ≤ 2 * ρ * c / a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hlog : 0 < 1 + Real.log (2 * ρ * c / a) := by linarith [Real.log_nonneg hratio]
  have hd : 0 < (Scale.dyExp 1 (s / 2) : ℝ) + 1 := by positivity
  unfold confinementDensity transverseDensity confinementConstant
  push_cast
  rw [div_one]
  field_simp
  <;> ring

lemma angular_dyadic_count_le {δ s : ℝ} (hδ : 0 < δ) (hδs : δ ≤ s) :
    Scale.dyExp 1 (s / 2) ≤ Scale.dyExp 2 δ := by
  have he : Scale.dyExp 1 (s / 2) = Scale.dyExp 2 s := by
    unfold Scale.dyExp
    congr 2
    ring
  rw [he]
  exact Scale.dyExp_le (by norm_num) hδ hδs

/-- With only polynomial aspect ratios, all constants and logarithms in
transverse filling cost one further arbitrarily small power. -/
theorem confinement_density_power_lower {ν : ℝ} (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
    ∀ a ρ c D s : ℝ, δ ≤ a → a ≤ ρ * c → ρ * c ≤ 1 → δ ^ ν ≤ D → δ ≤ s →
      δ ^ (5 * ν) ≤ confinementDensity a ρ c D s := by
  obtain ⟨d₁, hd₁, hC⟩ := constant_power_bound confinementConstant_pos (show 0 < ν / 4 by positivity)
  obtain ⟨d₂, hd₂, hdy⟩ := dyadic_size_power_bound (M := 2) (k := 1) (by norm_num)
    (by norm_num) (show 0 < ν / 4 by positivity)
  obtain ⟨d₃, hd₃, hlg⟩ := logarithm_power_bound (M := 2) (by norm_num) (show 0 < ν / 4 by positivity)
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃), ?_⟩
  intro δ hδ hδ1 hδd a ρ c D s hδa hac hρc hD hδs
  have ha : 0 < a := hδ.trans_le hδa
  have hC' := hC δ hδ (hδd.trans (min_le_left _ _))
  have hdy' := hdy δ hδ hδ1 (hδd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlg' := hlg δ hδ hδ1 (hδd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  rw [Real.rpow_one] at hdy'
  have hd : 0 < (Scale.dyExp 1 (s / 2) : ℝ) + 1 := by positivity
  have hdbound : (Scale.dyExp 1 (s / 2) : ℝ) + 1 ≤ δ ^ (-(ν / 4)) := by
    have hh := Nat.cast_le (α := ℝ).mpr (angular_dyadic_count_le hδ hδs)
    linarith
  have hratio : 1 ≤ 2 * ρ * c / a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hlog : 0 < 1 + Real.log (2 * ρ * c / a) := by linarith [Real.log_nonneg hratio]
  have hratioUpper : 2 * ρ * c / a ≤ 2 / δ := by
    apply (div_le_div_iff₀ ha hδ).mpr
    nlinarith
  have hlogUpper : 1 + Real.log (2 * ρ * c / a) ≤ δ ^ (-(ν / 4)) := by
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one hratio) hratioUpper
    linarith
  have hdenom : confinementConstant * ((Scale.dyExp 1 (s / 2) : ℝ) + 1) ^ 2 *
      (1 + Real.log (2 * ρ * c / a)) ≤ δ ^ (-ν) := by
    calc
      _ ≤ δ ^ (-(ν / 4)) * (δ ^ (-(ν / 4))) ^ 2 * δ ^ (-(ν / 4)) := by
        gcongr
      _ = δ ^ (-ν) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        push_cast
        ring
  rw [confinementDensity_formula ha hac]
  apply (le_div_iff₀ (show 0 < confinementConstant * ((Scale.dyExp 1 (s / 2) : ℝ) + 1) ^ 2 *
    (1 + Real.log (2 * ρ * c / a)) from mul_pos (mul_pos confinementConstant_pos (sq_pos_of_pos hd)) hlog)).mpr
  calc
    _ ≤ δ ^ (5 * ν) * δ ^ (-ν) := mul_le_mul_of_nonneg_left hdenom (Real.rpow_nonneg hδ.le _)
    _ = (δ ^ ν) ^ (4 : ℕ) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_mul_natCast hδ.le]
      congr 1
      push_cast
      ring
    _ ≤ D ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hD 4

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
