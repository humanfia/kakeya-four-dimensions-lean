import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedLayers
import Submission.Obl.k4_general_wide_layer_offset_comparison.ShortDomainMenus

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- Change only the common width; every original label and polynomial is kept. -/
def withWidth (L : ProjectedLayer α) (β : ℝ) : ProjectedLayer α := { L with β := β }

/-- Shrinking the moving norm interval retains the actual original layer.
The trajectory band is paid with an explicitly larger intrinsic loss. -/
theorem withWidth_valid {L : ProjectedLayer α} {p : Parent α}
    {k : ℕ} {s m H H' β : ℝ} (hL : L.Valid p k s m H)
    (hN : 0 < p.N k) (hH : 0 < H) (hHH : H ≤ H')
    (hβ : 0 < β) (hβL : β ≤ L.β) (hmotion : H * L.β ≤ H' * β)
    (hlow : p.N k ^ (-p.ℓ * s) / H' ≤ β)
    (hhigh : β ≤ H' * p.N k ^ (-p.ℓ * s)) :
    (L.withWidth β).Valid p k s m H' := by
  rcases hL with ⟨hLβ, hlo, hhi, hmeas, hdisj, hi, hbudget⟩
  have hH' : 0 < H' := hH.trans_le hHH
  have hA : 0 ≤ p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d := by positivity
  refine ⟨hβ, hlow, hhigh, hmeas, hdisj, ?_, ?_⟩
  · intro i
    obtain ⟨huv, hdeg, hnorm, hfit, hfloor⟩ := hi i
    refine ⟨huv.trans hHH, hdeg, ?_, ?_, ?_⟩
    · intro t ht w hw
      have hr₀ : 0 ≤ β / L.β := div_nonneg hβ.le hLβ.le
      have hr₁ : β / L.β ≤ 1 := (div_le_one hLβ).mpr hβL
      have hscaled : β / L.β * w ∈ Icc (-1 : ℝ) 1 := by
        apply abs_le.mp
        rw [abs_mul, abs_of_nonneg hr₀]
        simpa only [one_mul] using mul_le_mul hr₁ (abs_le.mpr hw) (abs_nonneg _) zero_le_one
      have hn := hnorm t ht _ hscaled
      have heq : L.β * (β / L.β * w) = β * w := by field_simp
      rw [heq] at hn
      exact hn.trans hHH
    · intro l hl
      obtain ⟨h0, h1, hf⟩ := hfit l hl
      refine ⟨h0, h1, fun t ht => ⟨(hf t ht).1.trans hmotion, ?_⟩⟩
      exact (hf t ht).2.trans (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hN.le _))
    · refine le_trans ?_ hfloor
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      calc
        p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d * β / H' ≤
            p.N k ^ (-m) * (p.N k ^ (-s)) ^ p.d * β / H :=
          div_le_div_of_nonneg_left (mul_nonneg hA hβ.le) hH hHH
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hβL hA) hH.le
  · calc
      _ ≤ ∑ i, L.referenceWeight p k s m i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul' _ le_rfl
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hβL hA)
      _ ≤ ENNReal.ofReal H := hbudget
      _ ≤ _ := ENNReal.ofReal_le_ofReal hHH

/-- Cap the common width at the fixed original slope mesh. The larger loss
is still intrinsic and all original assignment and predictor fields agree. -/
theorem capWidth_valid {L : ProjectedLayer α} {p : Parent α}
    {k : ℕ} {s m H g : ℝ} (hL : L.Valid p k s m H)
    (hN : 0 < p.N k) (hH : 1 ≤ H) (hg : 0 < g)
    (hβg : L.β ≤ H * g) (hlowg : p.N k ^ (-p.ℓ * s) / H ^ 2 ≤ g) :
    (L.withWidth (min L.β g)).Valid p k s m (H ^ 2) := by
  have hHH : H ≤ H ^ 2 := by nlinarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  apply withWidth_valid hL hN hHp hHH (lt_min hL.1 hg) (min_le_left _ _)
    (band_le_squared_loss hH hL.1.le hβg)
  · exact le_min ((div_le_div_of_nonneg_left (Real.rpow_nonneg hN.le _) hHp hHH).trans
      hL.2.1) hlowg
  · exact (min_le_left _ _).trans (hL.2.2.1.trans
      (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hN.le _)))

end ProjectedLayer

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
