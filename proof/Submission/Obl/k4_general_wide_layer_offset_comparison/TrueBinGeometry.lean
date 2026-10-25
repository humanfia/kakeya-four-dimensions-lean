import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeGeometry
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeSourceCaps
import Submission.Lib.K4ProjectedGroups.GroupCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/TrueBinGeometry.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Freezing the two fine major bins turns the true transverse packet into
one affine moving band, with the original independent transverse width. -/
theorem AtDepth.transverse_band_on_major_bin
    {k : ℕ} {s R χ : ℝ} (hat : p.AtDepth k s R) (hK : 0 ≤ p.K k) (hχ : 0 < χ)
    (hχwidth : χ ≤ (2 : ℝ) ^ (-(p.T k s : ℤ)) * p.N k ^ (-p.ℓ * s))
    (hχslope : χ ≤ p.N k ^ (-p.ℓ * s))
    (i : Fin (p.n k s)) {l : α} (hl : l ∈ p.A k s i)
    (z₀ v₀ : ℤ) (hz : ⌊p.b k l 0 / χ⌋ = z₀) (hv : ⌊p.b k l 3 / χ⌋ = v₀)
    {t : ℝ} (ht : t ∈ block (p.T k s) (p.j k s i)) :
    |(p.x k l t) 2 - (p.c k s i 2 + p.c k s i 4 * ((z₀ : ℝ) * χ)) -
      t * (p.c k s i 3 + p.c k s i 4 * ((v₀ : ℝ) * χ))| ≤
        (3 * p.K k) * ((2 : ℝ) ^ (-(p.T k s : ℤ)) * p.N k ^ (-p.ℓ * s)) ∧
    |p.b k l 4 - (p.c k s i 3 + p.c k s i 4 * ((v₀ : ℝ) * χ))| ≤
      (2 * p.K k) * p.N k ^ (-p.ℓ * s) := by
  let q := (2 : ℝ) ^ (-(p.T k s : ℤ))
  let g := p.N k ^ (-p.ℓ * s)
  have hrow := hat.2.2.2.2.1 i
  have hc := hrow.2.2.2.1 4
  have hgeo := hrow.2.2.2.2.2.1 l hl t ht
  have htunit := Submission.Obl.k4_balanced_native_packet_transport.Pullback.block_subset_unit
    (p.j k s i) ht
  have hmajor : |(p.x k l t) 1 - ((z₀ : ℝ) * χ + t * ((v₀ : ℝ) * χ))| ≤ 2 * χ := by
    simpa only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
      Matrix.cons_val_one, Matrix.cons_val_zero] using intercept_velocity_bin_tube hχ hz hv htunit
  have hvelocity : |p.b k l 3 - (v₀ : ℝ) * χ| ≤ χ := by
    obtain ⟨hlo, hhi⟩ := Submission.Lib.K4ProjectedGroups.floor_bounds hχ hv
    rw [abs_le]
    constructor <;> linarith
  constructor
  · calc
      _ = |((p.x k l t) 2 - p.c k s i 2 - t * p.c k s i 3 -
          p.c k s i 4 * (p.x k l t) 1) + p.c k s i 4 *
          ((p.x k l t) 1 - ((z₀ : ℝ) * χ + t * ((v₀ : ℝ) * χ)))| := by congr 1; ring
      _ ≤ |(p.x k l t) 2 - p.c k s i 2 - t * p.c k s i 3 -
          p.c k s i 4 * (p.x k l t) 1| + |p.c k s i 4 *
          ((p.x k l t) 1 - ((z₀ : ℝ) * χ + t * ((v₀ : ℝ) * χ)))| := abs_add_le _ _
      _ ≤ p.K k * q * g + p.K k * (2 * χ) := by
        rw [abs_mul]
        exact add_le_add hgeo.2.1 (mul_le_mul hc hmajor (abs_nonneg _) hK)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hχwidth hK
        dsimp [q, g] at *
        nlinarith
  · calc
      _ = |(p.b k l 4 - p.c k s i 3 - p.c k s i 4 * p.b k l 3) +
          p.c k s i 4 * (p.b k l 3 - (v₀ : ℝ) * χ)| := by congr 1; ring
      _ ≤ |p.b k l 4 - p.c k s i 3 - p.c k s i 4 * p.b k l 3| +
          |p.c k s i 4 * (p.b k l 3 - (v₀ : ℝ) * χ)| := abs_add_le _ _
      _ ≤ p.K k * g + p.K k * χ := by
        rw [abs_mul]
        exact add_le_add hgeo.2.2 (mul_le_mul hc hvelocity (abs_nonneg _) hK)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hχslope hK
        dsimp [g] at *
        nlinarith

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
