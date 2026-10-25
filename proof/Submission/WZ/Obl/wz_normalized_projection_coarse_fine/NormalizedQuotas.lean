-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.NormalizedQuotas.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.RescaledMass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.MaximalDensity

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric LeanEval.Analysis.WangZahlKakeya

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Original-grid Frostman quotas remain Frostman quotas after centering a coarse cell
and scaling its parameter radius to one. -/
theorem normalized_dyadic_quota {α : Type*} [DecidableEq α]
    (U : Finset α) (p : α → Space) (q₀ : Space) {j L : ℕ} (hjL : j ≤ L)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hcount : ∀ k, j ≤ k → k ≤ L → ∀ l : Fin 3 → ℤ,
      ((U.filter (fun a => dyadicLabel k (p a) = l)).card : ℝ) ≤
        (U.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s)) :
    ∀ k, k ≤ L - j + 1 → ∀ l : Fin 3 → ℤ,
      ((U.filter (fun a => dyadicLabel k
        (normalizedParameters (2 * ((2 : ℝ) ^ j)⁻¹) q₀ (p a)) = l)).card : ℝ) ≤
        108 * (((2 : ℝ) ^ k)⁻¹) ^ s * U.card := by
  intro k hk l
  let ρ := 2 * ((2 : ℝ) ^ j)⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let V := U.filter (fun a => dyadicLabel k (normalizedParameters ρ q₀ (p a)) = l)
  have hVU : V ⊆ U := Finset.filter_subset _ _
  have hN : 0 ≤ (U.card : ℝ) := Nat.cast_nonneg _
  by_cases hk2 : k < 2
  · have hside : (1 / 2 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ := by
      interval_cases k <;> norm_num
    have hside1 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := by
      interval_cases k <;> norm_num
    have hp : (1 / 2 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ s := by
      have hh := Real.rpow_le_rpow_of_exponent_ge (by positivity) hside1 hs1
      rw [Real.rpow_one] at hh
      exact hside.trans hh
    change (V.card : ℝ) ≤ _
    exact (Nat.cast_le.mpr (Finset.card_le_card hVU)).trans (by nlinarith)
  have h2k : 2 ≤ k := by omega
  let m := j + (k - 2)
  have hjm : j ≤ m := by dsimp [m]; omega
  have hmL : m ≤ L := by dsimp [m]; omega
  have hkm : (2 : ℝ) ^ k = 4 * (2 : ℝ) ^ (k - 2) := by
    calc
      (2 : ℝ) ^ k = 2 ^ (2 + (k - 2)) := by rw [Nat.add_sub_of_le h2k]
      _ = _ := by rw [pow_add]; norm_num
  have hratio : ((2 : ℝ) ^ m)⁻¹ / ((2 : ℝ) ^ j)⁻¹ = 4 * ((2 : ℝ) ^ k)⁻¹ := by
    dsimp [m]
    rw [pow_add, hkm]
    field_simp
  have hscale : 2 * ρ * ((2 : ℝ) ^ k)⁻¹ = ((2 : ℝ) ^ m)⁻¹ := by
    have hh := (div_eq_iff (by positivity : ((2 : ℝ) ^ j)⁻¹ ≠ 0)).mp hratio
    dsimp [ρ]
    nlinarith
  rcases V.eq_empty_or_nonempty with he | hV
  · change (V.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨b, hb⟩ := hV
  have hsub : V ⊆ U.filter (fun a => p a ∈ ball (p b) (((2 : ℝ) ^ m)⁻¹)) := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hd := dist_le_of_dyadicLabel_eq he
    rw [dist_normalizedParameters hρ] at hd
    have hm := (div_le_iff₀ hρ).mp hd
    refine Finset.mem_filter.mpr ⟨hVU ha, ?_⟩
    rw [mem_ball, ← hscale]
    have hroot : Real.sqrt 3 < 2 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [Real.sqrt_nonneg 3]
    have hp : 0 < ρ * ((2 : ℝ) ^ k)⁻¹ := by positivity
    nlinarith [mul_lt_mul_of_pos_right hroot hp]
  have hball := ball_count_le_of_dyadic_cells U p (hcount m hjm hmL) (p b) le_rfl
  have hpow : (4 : ℝ) ^ s ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hs1
  calc
    (V.card : ℝ) ≤ (U.filter (fun a => p a ∈ ball (p b) (((2 : ℝ) ^ m)⁻¹))).card := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ 3 ^ 3 * ((U.card : ℝ) * ((((2 : ℝ) ^ m)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s)) := hball
    _ = 27 * ((U.card : ℝ) * ((4 : ℝ) ^ s * ((((2 : ℝ) ^ k)⁻¹) ^ s))) := by
      rw [hratio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      norm_num
    _ ≤ 27 * ((U.card : ℝ) * (4 * ((((2 : ℝ) ^ k)⁻¹) ^ s))) := by gcongr
    _ = _ := by ring

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
