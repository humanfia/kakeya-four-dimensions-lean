import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Grid

/-!
# Anisotropic cells meeting a moving sheared box

Cells `(⌊t/δ⌋, ⌊Z/δ⌋, ⌊Y/Δ⌋)` with a separate height mesh `Δ`. This adapts x0699's
`rectangularGrid` (same obligation, `RectangularGrid.lean`) to a coarser last coordinate.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open Set
open Submission.Obl.k4_horizontal_supercritical_rate_candidates

noncomputable section

/-- Anisotropic cells meeting a sheared box with three independent widths. -/
def aniGrid (δ Δ A B C t₀ p r v w τ : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  (intervalBins δ t₀ A).biUnion fun a =>
    (intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
      (intervalBins Δ
        (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
        (C + (|w| + |τ| * (1 + |v|)) * δ)).image fun c => (a, b, c)

theorem floor_cell_abs {δ x : ℝ} (hδ : 0 < δ) : |x - (⌊x / δ⌋ : ℝ) * δ| ≤ δ := by
  have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (x / δ))
  have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x / δ))
  rw [abs_le]
  constructor <;> nlinarith only [h₀, h₁, hδ]

theorem mem_aniGrid {δ Δ A B C t₀ p r v w τ t Z Y : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (ht : |t - t₀| ≤ A)
    (hZ : |Z - (p + t * v)| ≤ B)
    (hY : |Y - (r - t * w) - τ * (Z - (p + t * v))| ≤ C) :
    (⌊t / δ⌋, ⌊Z / δ⌋, ⌊Y / Δ⌋) ∈ aniGrid δ Δ A B C t₀ p r v w τ := by
  set a := ⌊t / δ⌋
  set b := ⌊Z / δ⌋
  have htcell : |t - (a : ℝ) * δ| ≤ δ := floor_cell_abs hδ
  have hZcell : |Z - (b : ℝ) * δ| ≤ δ := floor_cell_abs hδ
  have hZanchor : |Z - (p + (a : ℝ) * δ * v)| ≤ B + |v| * δ := by
    calc
      _ = |(Z - (p + t * v)) + (t - (a : ℝ) * δ) * v| := by congr 1; ring
      _ ≤ |Z - (p + t * v)| + |(t - (a : ℝ) * δ) * v| := abs_add_le _ _
      _ ≤ B + |v| * δ := by
        rw [abs_mul, mul_comm |t - (a : ℝ) * δ|]
        exact add_le_add hZ (mul_le_mul_of_nonneg_left htcell (abs_nonneg _))
  have hYanchor :
      |Y - (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))| ≤
        C + (|w| + |τ| * (1 + |v|)) * δ := by
    have heq :
        Y - (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v))) =
        (Y - (r - t * w) - τ * (Z - (p + t * v))) -
          (t - (a : ℝ) * δ) * w +
          τ * ((Z - (b : ℝ) * δ) - (t - (a : ℝ) * δ) * v) := by ring
    rw [heq]
    calc
      _ ≤ |Y - (r - t * w) - τ * (Z - (p + t * v))| +
          |(t - (a : ℝ) * δ) * w| +
          |τ| * (|Z - (b : ℝ) * δ| + |(t - (a : ℝ) * δ) * v|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ C + δ * |w| + |τ| * (δ + δ * |v|) := by
        simp only [abs_mul]
        gcongr
      _ = _ := by ring
  apply Finset.mem_biUnion.mpr
  refine ⟨a, mem_intervalBins hδ ht, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨b, mem_intervalBins hδ hZanchor, Finset.mem_image.mpr ?_⟩
  exact ⟨⌊Y / Δ⌋, mem_intervalBins hΔ hYanchor, rfl⟩

theorem card_aniGrid {δ Δ A B C : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (t₀ p r v w τ : ℝ) :
    ((aniGrid δ Δ A B C t₀ p r v w τ).card : ℝ) ≤
      (2 * A / δ + 5) * (2 * (B + |v| * δ) / δ + 5) *
        (2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / Δ + 5) := by
  let BZ := 2 * (B + |v| * δ) / δ + 5
  let BY := 2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / Δ + 5
  have hBY : 0 ≤ BY := by dsimp [BY]; positivity
  have hBZ : 0 ≤ BZ := by dsimp [BZ]; positivity
  have hinner (a : ℤ) :
      (((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
        (intervalBins Δ
          (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
          (C + (|w| + |τ| * (1 + |v|)) * δ)).image
          fun c => (a, b, c)).card : ℝ) ≤ BZ * BY := by
    calc
      _ ≤ ∑ b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ),
          (((intervalBins Δ
            (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (C + (|w| + |τ| * (1 + |v|)) * δ)).image
            fun c => (a, b, c)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ), BY := by
        apply Finset.sum_le_sum
        intro b _
        exact (Nat.cast_le.mpr Finset.card_image_le).trans (card_intervalBins hΔ (by positivity) _)
      _ = ((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).card : ℝ) * BY := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ BZ * BY := mul_le_mul_of_nonneg_right (card_intervalBins hδ (by positivity) _) hBY
  calc
    _ ≤ ∑ a ∈ intervalBins δ t₀ A,
        (((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
          (intervalBins Δ
            (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (C + (|w| + |τ| * (1 + |v|)) * δ)).image
            fun c => (a, b, c)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ intervalBins δ t₀ A, BZ * BY := Finset.sum_le_sum (fun a _ => hinner a)
    _ = ((intervalBins δ t₀ A).card : ℝ) * (BZ * BY) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * A / δ + 5) * (BZ * BY) :=
      mul_le_mul_of_nonneg_right (card_intervalBins hδ hA _) (mul_nonneg hBZ hBY)
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
