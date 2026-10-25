import Submission.Obl.k4_scalar_grid_cartesian_field.Growth

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The original angular cap is available at every fixed positive depth, before a slow diagonal. -/
theorem original_angular_cap_fixed (data : Data) (hcap : capHyp data) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ k in atTop, ∀ g : Fin (data.W k), ∀ c : ℤ,
      data.π k g (vel data k b c) ≤ ENNReal.ofReal (data.K k * data.N k ^ (-data.S * b)) := by
  let R := max 2 (max (2 / b) b)
  have hR : 1 < R := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  have hRb : 2 / b ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hbR : b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRinv : R⁻¹ ≤ b := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < R)]
    have h := (div_le_iff₀ hb).mp hRb
    nlinarith
  have hRinvone : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hR.le
  filter_upwards [hcap R hR] with k hk
  intro g
  exact (hk g 1 1 b hRinvone hR.le hRinvone hR.le hRinv hbR).1

/-- Choose inverse-subpower angular separation after the actual palette loss is fixed.
The original prior then gives a uniformly small fraction in every separation bin. -/
theorem exists_original_angular_mesh (data : Data) (hs : scaleHyp data) (hcap : capHyp data)
    (A : ℕ → ℝ) (hA : subpower data A)
    (Q : ℝ → ℕ → Prop) (hQ : ∀ b : ℝ, 0 < b → ∀ᶠ k in atTop, Q b k) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ Tendsto b atTop (nhds 0) ∧
      subpower data (fun k => data.N k ^ b k) ∧
      ∀ᶠ k in atTop, (∀ (g : Fin (data.W k)) (c : ℤ),
        ENNReal.ofReal (16 * A k) * data.π k g (vel data k (b k) c) ≤ 1) ∧ Q (b k) k := by
  have hN : ∀ k, 0 < data.N k := fun k => by linarith [hs.1 k]
  have hK := hs.2.2.1
  have hS : 0 < data.S := hs.2.2.2.2.2.2.2
  have hAK : SubpowerLoss data.N (fun k => A k * data.K k) :=
    Submission.Obl.k4_tempered_grid_selection.subpower_mul hN hA hK
  let P : ℝ → ℕ → Prop := fun b k =>
    ∀ (g : Fin (data.W k)) (c : ℤ),
      ENNReal.ofReal (16 * A k) * data.π k g (vel data k b c) ≤ 1
  have hP (b : ℝ) (hb : 0 < b) : ∀ᶠ k in atTop, P b k := by
    have hnum := eventually_polynomial_subpower_le
      (fun k => by linarith [hs.1 k]) hs.2.1 hAK
      (by norm_num : (1 : ℝ) ≤ 16) 1 (mul_pos hS hb)
    filter_upwards [original_angular_cap_fixed data hcap hb, hnum] with k hk hn
    intro g c
    have hreal : (16 * A k) * (data.K k * data.N k ^ (-data.S * b)) ≤ 1 := by
      calc
        _ = (16 * (A k * data.K k)) * data.N k ^ (-data.S * b) := by ring
        _ ≤ data.N k ^ (data.S * b) * data.N k ^ (-data.S * b) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hN k).le _)
          simpa only [pow_one] using hn
        _ = 1 := by rw [← Real.rpow_add (hN k)]; simp
    calc
      _ ≤ ENNReal.ofReal (16 * A k) * ENNReal.ofReal (data.K k * data.N k ^ (-data.S * b)) :=
        mul_le_mul' le_rfl (hk g c)
      _ = ENNReal.ofReal ((16 * A k) * (data.K k * data.N k ^ (-data.S * b))) :=
        (ENNReal.ofReal_mul (by have := hA.1 k; positivity)).symm
      _ ≤ 1 := (ENNReal.ofReal_le_ofReal hreal).trans_eq (by norm_num)
  exact exists_subpower_accuracy (fun k => by linarith [hs.1 k]) (fun b k => P b k ∧ Q b k)
    (fun b hb => (hP b hb).and (hQ b hb))

/-- Relative palette domination at the selected mesh gives the core's separated-bin inequality. -/
theorem separation_from_original_palette {μevent μcell πbin : ENNReal} {A : ℝ}
    (hA : 0 ≤ A) (hpalette : μevent ≤ ENNReal.ofReal A * μcell * πbin)
    (hsmall : ENNReal.ofReal (16 * A) * πbin ≤ 1) : 16 * μevent ≤ μcell := by
  calc
    _ ≤ 16 * (ENNReal.ofReal A * μcell * πbin) := mul_le_mul' le_rfl hpalette
    _ = (ENNReal.ofReal (16 * A) * πbin) * μcell := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16), ENNReal.ofReal_ofNat]
      ac_rfl
    _ ≤ 1 * μcell := mul_le_mul' hsmall le_rfl
    _ = _ := one_mul _

end Submission.Obl.k4_scalar_grid_cartesian_field
