-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.MassTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Normalization

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

lemma cancel_volume_factor {J : ℝ} (hJ : 0 < J) {a b : ℝ≥0∞}
    (h : ENNReal.ofReal J * a ≤ ENNReal.ofReal J * b) : a ≤ b := by
  have h₀ : ENNReal.ofReal J ≠ 0 := (ENNReal.ofReal_pos.mpr hJ).ne'
  calc
    a = (ENNReal.ofReal J)⁻¹ * (ENNReal.ofReal J * a) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h₀ ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal J)⁻¹ * (ENNReal.ofReal J * b) := mul_le_mul_right h _
    _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h₀ ENNReal.ofReal_ne_top, one_mul]

lemma pullback_shadings (f : Space ≃ᴬ[ℝ] Space) {J : ℝ} (hJ : 0 < J)
    (hvol : ∀ W : Set Space, volume (f '' W) = ENNReal.ofReal J * volume W)
    {n : ℕ} (Y Z : Fin n → Set Space) (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ f '' Y i)
    {S : Finset (Fin n)} {a : ℝ}
    (hmass : ENNReal.ofReal a * (∑ i, volume (f '' Y i)) ≤ ∑ i ∈ S, volume (Z i)) :
    (∀ i, MeasurableSet (f ⁻¹' Z i) ∧ f ⁻¹' Z i ⊆ Y i) ∧
      ENNReal.ofReal a * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (f ⁻¹' Z i) := by
  have hdata (i) : MeasurableSet (f ⁻¹' Z i) ∧ f ⁻¹' Z i ⊆ Y i := by
    refine ⟨(hZ i).1.preimage f.continuous.measurable, ?_⟩
    intro p hp
    obtain ⟨q, hq, he⟩ := (hZ i).2 hp
    exact f.injective he ▸ hq
  refine ⟨hdata, ?_⟩
  have hZvol (i) : volume (Z i) = ENNReal.ofReal J * volume (f ⁻¹' Z i) := by
    rw [← hvol, f.surjective.image_preimage]
  simp_rw [hvol, hZvol] at hmass
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hmass
  apply cancel_volume_factor hJ
  simpa only [mul_left_comm] using hmass

lemma absorb_finite_weight {d τ : ℝ} (hd : 0 < d) {q : ℕ}
    (hsmall : d ^ τ * (q : ℝ) ≤ 1) {a b : ℝ≥0∞}
    (h : a ≤ (q : ℝ≥0∞) * b) : ENNReal.ofReal (d ^ τ) * a ≤ b := by
  have hc : ENNReal.ofReal (d ^ τ) * (q : ℝ≥0∞) ≤ 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd _).le]
    exact (ENNReal.ofReal_le_ofReal hsmall).trans_eq (by norm_num)
  calc
    _ ≤ ENNReal.ofReal (d ^ τ) * ((q : ℝ≥0∞) * b) := mul_le_mul_right h _
    _ = (ENNReal.ofReal (d ^ τ) * (q : ℝ≥0∞)) * b := (mul_assoc _ _ _).symm
    _ ≤ 1 * b := mul_le_mul_left hc _
    _ = b := one_mul _

lemma retained_three_powers {d θ τ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hθτ : θ ≤ τ)
    {a b c e : ℝ≥0∞}
    (h₁ : ENNReal.ofReal (d ^ θ) * a ≤ b)
    (h₂ : ENNReal.ofReal (d ^ τ) * b ≤ c)
    (h₃ : ENNReal.ofReal (d ^ τ) * c ≤ e) :
    ENNReal.ofReal (d ^ (3 * τ)) * a ≤ e := by
  calc
    _ ≤ ENNReal.ofReal (d ^ (τ + τ + θ)) * a :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))) _
    _ = ENNReal.ofReal (d ^ τ) * (ENNReal.ofReal (d ^ τ) * (ENNReal.ofReal (d ^ θ) * a)) := by
      rw [Real.rpow_add hd, Real.rpow_add hd,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ac_rfl
    _ ≤ ENNReal.ofReal (d ^ τ) * (ENNReal.ofReal (d ^ τ) * b) := by gcongr
    _ ≤ ENNReal.ofReal (d ^ τ) * c := mul_le_mul_right h₂ _
    _ ≤ e := h₃

lemma retained_card_of_mass {d τ s : ℝ} (hd : 0 < d) (hs : 0 < s) (hs1 : s ≤ 1)
    {n m : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (j : Fin m → Fin n) (Z : Fin m → Set Space) (S : Finset (Fin m))
    (hv : ∀ i, ‖v i‖ = 1)
    (hZ : ∀ i, Z i ⊆ tube s (x (j i)) (v (j i)))
    (hden : ENNReal.ofReal (d ^ τ * n * s ^ 2) ≤ ∑ i, volume (Y i))
    (hmass : ENNReal.ofReal (d ^ (3 * τ)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i)) :
    (d ^ (4 * τ) / 56) * n ≤ S.card := by
  have hup : (∑ i ∈ S, volume (Z i)) ≤ ENNReal.ofReal (56 * (S.card : ℝ) * s ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ S, ENNReal.ofReal (56 * s ^ 2) := Finset.sum_le_sum (fun i _ =>
        (measure_mono (hZ i)).trans
          (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hs.le hs1 _ _ (hv _)))
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  have hlo : ENNReal.ofReal (d ^ (4 * τ) * n * s ^ 2) ≤ ENNReal.ofReal (56 * (S.card : ℝ) * s ^ 2) := by
    calc
      _ = ENNReal.ofReal (d ^ (3 * τ)) * ENNReal.ofReal (d ^ τ * n * s ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), show 4 * τ = 3 * τ + τ by ring, Real.rpow_add hd]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (d ^ (3 * τ)) * (∑ i, volume (Y i)) := mul_le_mul_right hden _
      _ ≤ _ := hmass.trans hup
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * (S.card : ℝ) * s ^ 2)).mp hlo
  have hh' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp hh
  linarith

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
