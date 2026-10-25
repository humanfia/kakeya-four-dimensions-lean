-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.AssemblyHelpers
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Admissibility

namespace WangZahlLot.Obl.wz_separated_scales_gain

open WangZahlLot.Obl.wz_nonflat_factored_improvement

set_option maxHeartbeats 600000 in
/-- Choose all losses before the fine scale, uniformly over the two parent scales. -/
theorem choose_separated_parameters {ζ e ηF ηM ηO : ℝ}
    (hζ : 0 < ζ) (he : 0 < e) (hηF : 0 < ηF) (hηM : 0 < ηM) (hηO : 0 < ηO) :
    ∃ ζ₀ η ν t d : ℝ, ∃ K : ℕ,
      0 < ζ₀ ∧ 0 < η ∧ 0 < ν ∧ 0 < t ∧ 0 < d ∧ d ≤ 1 ∧ 0 < K ∧
      3 * η + 2 * ν + 4 * t + 4 * ζ₀ ≤ e ∧
      ∀ ζ₂ δ τ ρ : ℝ, 0 < ζ₂ → ζ₂ ≤ ζ₀ → 0 < δ → δ ≤ d →
        δ ≤ τ → τ < ρ → ρ ≤ 1 → τ ≤ δ ^ ζ * ρ →
        ScaleConditions δ τ ρ (δ ^ η) (δ ^ ν) (δ ^ (-ζ₂)) (δ ^ t) ηF ηM ηO K := by
  let Z := ζ * ηM
  have hZ : 0 < Z := mul_pos hζ hηM
  let ν := e / 64
  let t := e / 64
  have hν : 0 < ν := by dsimp [ν]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  let ζ₀ := min (e / 64) (Z / 16)
  have hζ₀ : 0 < ζ₀ := lt_min (by positivity) (by positivity)
  have hζ₀e : ζ₀ ≤ e / 64 := min_le_left _ _
  have hζ₀Z : ζ₀ ≤ Z / 16 := min_le_right _ _
  let η := min 1 (min (e / 64) (min (Z / 16) (min (t * ηF / 2) (t * ηO / 2))))
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : η ≤ e / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hηZ : η ≤ Z / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηF' : η ≤ t * ηF / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hηO' : η ≤ t * ηO / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let K := ⌈4 / ν⌉₊
  have hK : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKbound : 4 ≤ ν * K := by
    have hh := (div_le_iff₀ hν).mp (Nat.le_ceil (4 / ν))
    dsimp [K]
    linarith
  have hκ : 0 < fineContraction := by norm_num
  have hfrac := retainedFraction_pos
  let C := max (16 / fineContraction)
    (224 * K * (2048 * K) / (fineContraction ^ 3 * retainedFraction))
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  obtain ⟨dF, hdF, HF⟩ := exists_small_rpow (by positivity : 0 < t * ηF / 2)
    (by positivity : 0 < fineContraction / (64 * K))
  obtain ⟨dM, hdM, HM⟩ := exists_small_rpow (by positivity : 0 < Z / 2)
    (by positivity : 0 < fineContraction / ((2048 * K) * (64 * K)))
  obtain ⟨dO, hdO, HO⟩ := exists_small_rpow (by positivity : 0 < t * ηO / 2)
    (by positivity : 0 < fineContraction / ((2048 * K) ^ 2 * 16))
  obtain ⟨dN, hdN, HN⟩ := exists_small_rpow (by positivity : 0 < Z / 2) (inv_pos.mpr hC)
  let d : ℝ := min (1 / (576 * 2048 * K)) (min dF (min dM (min dO dN)))
  have hd : 0 < d := lt_min (by positivity) (lt_min hdF (lt_min hdM (lt_min hdO hdN)))
  have hdcut : d ≤ 1 / (576 * 2048 * K) := min_le_left _ _
  have hd1 : d ≤ 1 := hdcut.trans ((div_le_one (by positivity)).mpr (by linarith))
  refine ⟨ζ₀, η, ν, t, d, K, hζ₀, hη, hν, ht, hd, hd1, hK, ?_, ?_⟩
  · dsimp [ν, t]
    linarith
  intro ζ₂ δ τ ρ hζ₂ hζ₂0 hδ hδd hδτ hτρ hρ1 hsep
  have hδ1 : δ ≤ 1 := hδd.trans hd1
  have hτ : 0 < τ := hδ.trans_le hδτ
  have hρ : 0 < ρ := hτ.trans hτρ
  have hτ1 : τ ≤ 1 := hτρ.le.trans hρ1
  have hδF : δ ≤ dF := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδM : δ ≤ dM := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδO : δ ≤ dO := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδN : δ ≤ dN := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hδcut : δ ≤ 1 / (576 * 2048 * K) := hδd.trans hdcut
  have hδeta : δ ≤ δ ^ η := Real.self_le_rpow_of_le_one hδ.le hδ1 hη1
  have hθ : (δ ^ ν) ^ K ≤ δ ^ 4 := by
    rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_natCast δ 4]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hKbound
  have hcut : 288 * (δ ^ ν) ^ K ≤ (δ ^ η / (2048 * K)) * δ ^ 2 / 2 := by
    have hsmall : 288 * δ ≤ 1 / (2 * (2048 * K)) := by
      convert mul_le_mul_of_nonneg_left hδcut (by norm_num : (0 : ℝ) ≤ 288) using 1 <;> ring
    calc
      _ ≤ 288 * δ ^ 4 := mul_le_mul_of_nonneg_left hθ (by norm_num)
      _ = (288 * δ) * (δ * δ ^ 2) := by ring
      _ ≤ (1 / (2 * (2048 * K))) * (δ * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ ≤ (1 / (2 * (2048 * K))) * (δ ^ η * δ ^ 2) := by gcongr
      _ = _ := by ring
  have hlamdiv : δ ^ η / (2048 * K) ≤ δ ^ η := by
    exact div_le_self (by positivity) (by linarith)
  have hζ₂Z : ζ₂ ≤ Z / 16 := hζ₂0.trans hζ₀Z
  have hneg := absorb_power_constant hδ hδ1 hC (HN δ hδ hδN)
    (show 2 * ζ₂ + η ≤ Z / 2 by linarith)
  have hr : 0 < fineRadius τ ρ := by dsimp [fineRadius]; positivity
  have hrbound : fineRadius τ ρ ≤ δ ^ ζ :=
    (fine_radius_le hτ.le hρ).trans ((div_le_iff₀ hρ).mpr hsep)
  have hrpow : (fineRadius τ ρ) ^ ηM ≤ δ ^ Z := by
    have hh := Real.rpow_le_rpow hr.le hrbound hηM.le
    rwa [← Real.rpow_mul hδ.le] at hh
  have hrneg : δ ^ (-Z) ≤ (fineRadius τ ρ) ^ (-ηM) := by
    have hh := Real.rpow_le_rpow_of_nonpos hr hrbound (by linarith : -ηM ≤ 0)
    rw [← Real.rpow_mul hδ.le] at hh
    convert hh using 1 <;> dsimp [Z] <;> congr 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ht2 : τ ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ 288 * (δ ^ ν) ^ K := mul_le_of_le_one_right (by positivity) ht2
      _ ≤ (δ ^ η / (2048 * K)) * δ ^ 2 / 2 := hcut
      _ ≤ _ := by gcongr
  · have hr2 : ρ ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ 288 * (δ ^ ν) ^ K := mul_le_of_le_one_right (by positivity) hr2
      _ ≤ (δ ^ η / (2048 * K)) * δ ^ 2 / 2 := hcut
      _ ≤ _ := by gcongr
  · intro hscale
    have hrad : (fineRadius δ τ) ^ ηF ≤ δ ^ (t * ηF) := by
      have hh := Real.rpow_le_rpow (by dsimp [fineRadius]; positivity : 0 ≤ fineRadius δ τ)
        ((fine_radius_le hδ.le hτ).trans hscale) hηF.le
      rwa [← Real.rpow_mul hδ.le] at hh
    have hh := hrad.trans (power_density_bound hδ hδ1 hηF' (HF δ hδ hδF))
    convert hh using 1 <;> ring
  · have hh := hrpow.trans (power_density_bound hδ hδ1 (by linarith : η ≤ Z / 2) (HM δ hδ hδM))
    convert hh using 1 <;> ring
  · apply le_trans _ (hneg.trans hrneg)
    calc
      _ = (16 / fineContraction) * δ ^ (-ζ₂) := by ring
      _ ≤ C * δ ^ (-(2 * ζ₂ + η)) := mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (by positivity) hC.le
  · apply le_trans _ (hneg.trans hrneg)
    have hid : 224 * K * (δ ^ (-ζ₂)) ^ 2 /
        (fineContraction ^ 3 * retainedFraction * (δ ^ η / (2048 * K))) =
        (224 * K * (2048 * K) / (fineContraction ^ 3 * retainedFraction)) * δ ^ (-(2 * ζ₂ + η)) := by
      calc
        _ = (224 * K * (2048 * K) / (fineContraction ^ 3 * retainedFraction)) *
            ((δ ^ (-ζ₂)) ^ 2 * (δ ^ η)⁻¹) := by field_simp <;> ring
        _ = _ := by
          rw [← Real.rpow_neg hδ.le, ← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
          congr 2
          norm_num
          ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro hscale
    have hrad : (fineRadius ρ 1) ^ ηO ≤ δ ^ (t * ηO) := by
      have hr1 : fineRadius ρ 1 ≤ ρ := by
        simpa only [div_one] using fine_radius_le hρ.le (by norm_num : (0 : ℝ) < 1)
      have hh := Real.rpow_le_rpow (by dsimp [fineRadius]; positivity : 0 ≤ fineRadius ρ 1)
        (hr1.trans hscale) hηO.le
      rwa [← Real.rpow_mul hδ.le] at hh
    have hh := hrad.trans (power_density_bound hδ hδ1 hηO' (HO δ hδ hδO))
    convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_separated_scales_gain
