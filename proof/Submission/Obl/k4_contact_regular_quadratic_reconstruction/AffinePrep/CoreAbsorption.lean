import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Powers

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open Filter
open Submission.Lib.K4QuadraticSheetCore
open Submission.Obl.k4_contact_fine_labels_from_coarse_cover

noncomputable section

/-- A fixed contact buffer absorbs all three core errors uniformly in the
coarse block and the unit-box envelope. The fine mesh exponent is unrestricted
above its stated lower bound. -/
theorem eventually_core_absorption
    (N K : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {e₀ τ M Cs : ℝ} (he : 0 < e₀) (hτ : 0 < τ)
    (hbuffer : 82 * τ ≤ e₀ / 4) (hM : 81 * τ + 1 ≤ M) (hCs : 0 < Cs)
    (hK : ∀ᶠ k in atTop, K k ≤ N k ^ τ) :
    ∀ᶠ k in atTop, ∀ q B : ℝ, 0 < q → 1 ≤ B →
      q⁻¹ ≤ K k * N k ^ (e₀ / 4) →
      let Λ := N k ^ τ
      let hm := N k ^ (-M)
      let εc := N k ^ (-e₀) / q / (8 * B)
      1 ≤ Λ ∧ εc ≤ 1 ∧
      4 * Cs * remezC 4 Λ * (3 * hm) ≤ 1 ∧
      8 * discBudget Cs Λ * (3 * hm) * Λ ^ 2 ≤ 1 ∧
      192 * Cs * sffKappa Cs Λ * (εc + 3 * hm) * Λ ^ 2 ≤ 1 ∧
      cubeErr Cs Λ ≤ N k ^ (81 * τ) ∧
      ∀ ε c : ℝ, 81 * τ ≤ ε → 0 ≤ c →
        c * cubeErr Cs Λ ≤ N k ^ ε * c := by
  obtain ⟨A, hA, hbudget⟩ := cube_error_power_budget Cs hCs
  have hAlate : ∀ᶠ k in atTop, A ≤ N k ^ τ :=
    ((tendsto_rpow_atTop hτ).comp hN).eventually_ge_atTop A
  have htwo : ∀ᶠ k in atTop, (2 : ℝ) ≤ N k ^ (e₀ / 2) :=
    ((tendsto_rpow_atTop (by linarith only [he] : 0 < e₀ / 2)).comp hN).eventually_ge_atTop 2
  filter_upwards [hK, hAlate, hN.eventually_ge_atTop 6, htwo] with k hKk hAk hNk htwo
  intro q B hq hB hqbound
  let Λ := N k ^ τ
  let hm := N k ^ (-M)
  let εc := N k ^ (-e₀) / q / (8 * B)
  have hN0 : 0 < N k := by linarith only [hNk]
  have hN1 : 1 ≤ N k := by linarith only [hNk]
  have hΛ : 1 ≤ Λ := hA.trans hAk
  have hεc : 0 ≤ εc := by dsimp [εc]; positivity
  have hhm : 0 ≤ hm := by dsimp [hm]; positivity
  have hpow : Λ ^ (81 : ℕ) = N k ^ (81 * τ) := by
    dsimp [Λ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hcontact : εc ≤ N k ^ (τ - 3 * e₀ / 4) := by
    calc
      εc = (N k ^ (-e₀) * q⁻¹) / (8 * B) := by
        dsimp [εc]
        rw [div_eq_mul_inv (N k ^ (-e₀)) q]
      _ ≤ N k ^ (-e₀) * q⁻¹ := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
        exact le_mul_of_one_le_right (by positivity) (by linarith only [hB])
      _ ≤ N k ^ (-e₀) * (K k * N k ^ (e₀ / 4)) :=
        mul_le_mul_of_nonneg_left hqbound (by positivity)
      _ ≤ N k ^ (-e₀) * (N k ^ τ * N k ^ (e₀ / 4)) := by gcongr
      _ = N k ^ (τ - 3 * e₀ / 4) := by
        rw [← mul_assoc, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
        congr 1
        ring
  have hcontactSmall : Λ ^ (81 : ℕ) * εc ≤ (1 : ℝ) / 2 := by
    rw [hpow]
    calc
      _ ≤ N k ^ (81 * τ) * N k ^ (τ - 3 * e₀ / 4) :=
        mul_le_mul_of_nonneg_left hcontact (by positivity)
      _ = N k ^ (82 * τ - 3 * e₀ / 4) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ N k ^ (-e₀ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hbuffer])
      _ = (N k ^ (e₀ / 2))⁻¹ := by
        rw [show -e₀ / 2 = -(e₀ / 2) by ring, Real.rpow_neg hN0.le]
      _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) htwo
      _ = _ := by norm_num
  have hmeshSmall : Λ ^ (81 : ℕ) * (3 * hm) ≤ (1 : ℝ) / 2 := by
    rw [hpow]
    calc
      _ = 3 * (N k ^ (81 * τ) * N k ^ (-M)) := by dsimp [hm]; ring
      _ = 3 * N k ^ (81 * τ - M) := by rw [← Real.rpow_add hN0]; rfl
      _ ≤ 3 * N k ^ (-1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hM])
      _ = 3 / N k := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ (1 : ℝ) / 2 := (div_le_iff₀ hN0).mpr (by linarith only [hNk])
  have hsmall : Λ ^ (81 : ℕ) * (εc + 3 * hm) ≤ 1 := by
    rw [mul_add]
    linarith only [hcontactSmall, hmeshSmall]
  obtain ⟨hloss, hconditions⟩ := hbudget Λ εc (3 * hm) hAk hεc (by positivity)
  obtain ⟨hs1, hs2, hs3⟩ := hconditions hsmall
  have hloss' : cubeErr Cs Λ ≤ N k ^ (81 * τ) := hloss.trans_eq hpow
  have hcon : εc ≤ 1 :=
    (le_mul_of_one_le_left hεc (show 1 ≤ Λ ^ (81 : ℕ) from one_le_pow₀ hΛ)).trans
      (hcontactSmall.trans (by norm_num : (1 : ℝ) / 2 ≤ 1))
  refine ⟨hΛ, hcon, hs1, hs2, hs3, hloss', ?_⟩
  intro ε c hε hc
  calc
    c * cubeErr Cs Λ ≤ c * N k ^ (81 * τ) := mul_le_mul_of_nonneg_left hloss' hc
    _ ≤ N k ^ ε * c := by
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hε) hc

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
