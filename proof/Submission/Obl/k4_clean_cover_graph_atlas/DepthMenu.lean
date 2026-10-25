import Submission.Obl.k4_clean_cover_graph_atlas.FiniteInterface

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Set

/-- Both old and candidate cleaning depths lie in the original depth interval. -/
theorem menuDepth_mem {L s h δ₀ : ℝ} (hL : 0 ≤ L) :
    menuDepth L s h δ₀ ∈ Icc 0 L :=
  ⟨le_min hL (le_max_left _ _), min_le_left _ _⟩

-- Adapted from this LOT tree o194/x0672, 69d09a7b, FixedDepths.lean.
/-- The candidate menu point lies between the old and improved depths. -/
theorem menuDepth_candidate_spec {L s h δ₀ r : ℝ}
    (hL : 0 < L) (hh : 0 < h) (hδ₀ : 0 ≤ δ₀) (hδh : δ₀ ≤ h / 4)
    (hr : 0 < r) (hnear : |r - s * L| ≤ δ₀ * L) (hroom : r + 2 * h * L ≤ L) :
    r ≤ menuDepth L s h δ₀ ∧ menuDepth L s h δ₀ ≤ r + h * L ∧
      r + h * L - 3 * δ₀ * L ≤ menuDepth L s h δ₀ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hnear
  have he : 0 ≤ δ₀ * L := mul_nonneg hδ₀ hL.le
  have hmargin : 0 < (h - 3 * δ₀) * L := mul_pos (by linarith) hL
  have hraw : 0 ≤ s * L + h * L - 2 * δ₀ * L := by nlinarith
  have hrawL : s * L + h * L - 2 * δ₀ * L ≤ L := by nlinarith [mul_pos hh hL]
  rw [menuDepth, max_eq_right hraw, min_eq_right hrawL]
  constructor
  · nlinarith
  · constructor <;> nlinarith

/-- The old menu point is at most three input tolerances below the moving old depth. -/
theorem menuDepth_old_spec {L s δ₀ r : ℝ}
    (hL : 0 ≤ L) (hδ₀ : 0 ≤ δ₀) (hr : 0 ≤ r) (hrL : r ≤ L)
    (hnear : |r - s * L| ≤ δ₀ * L) :
    menuDepth L s 0 δ₀ ≤ r ∧ r - 3 * δ₀ * L ≤ menuDepth L s 0 δ₀ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hnear
  have hδL : 0 ≤ δ₀ * L := mul_nonneg hδ₀ hL
  have hmax : max 0 (s * L - 2 * δ₀ * L) ≤ r := max_le hr (by linarith)
  simp only [menuDepth, zero_mul, add_zero]
  rw [min_eq_right (hmax.trans hrL)]
  exact ⟨hmax, (by linarith : r - 3 * δ₀ * L ≤ s * L - 2 * δ₀ * L).trans (le_max_right _ _)⟩

-- Adapted from this LOT tree o194/x0672, 69d09a7b, FixedDepths.lean.
/-- The fixed-depth profile increment cancels the dimension part of candidate counting. -/
theorem menuDepth_profile_increment {f : ℝ → ℝ} {L d δ₀ r q h : ℝ}
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hδ₀ : 0 ≤ δ₀)
    (hr : r ∈ Icc 0 L) (hq : q ∈ Icc 0 L)
    (hf : ∀ x ∈ Icc 0 L, |f x - f 0 - d * x| ≤ δ₀ * L)
    (hlo : r + h * L - 3 * δ₀ * L ≤ q) (hhi : q ≤ r + h * L) :
    d * h * L - 5 * δ₀ * L ≤ f q - f r ∧ f q - f r ≤ d * h * L + 2 * δ₀ * L := by
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hf r hr)
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp (hf q hq)
  have ha := mul_le_mul_of_nonneg_left hlo hd
  have hb := mul_le_mul_of_nonneg_left hhi hd
  have hc := mul_le_mul_of_nonneg_right hd1 (mul_nonneg hδ₀ hL)
  constructor <;> nlinarith

/-- Moving from the old fixed menu point to its path depth costs only tolerance. -/
theorem menuDepth_old_profile {f : ℝ → ℝ} {L s d δ₀ r : ℝ}
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hδ₀ : 0 ≤ δ₀)
    (hr : r ∈ Icc 0 L) (hnear : |r - s * L| ≤ δ₀ * L)
    (hf : ∀ x ∈ Icc 0 L, |f x - f 0 - d * x| ≤ δ₀ * L) :
    f r - f (menuDepth L s 0 δ₀) ≤ 5 * δ₀ * L := by
  have hq := menuDepth_old_spec hL hδ₀ hr.1 hr.2 hnear
  have hqm := menuDepth_mem (s := s) (h := 0) (δ₀ := δ₀) hL
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hf r hr)
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp (hf _ hqm)
  have hmul := mul_le_mul_of_nonneg_left hq.2 hd
  have hδmul := mul_le_mul_of_nonneg_right hd1 (mul_nonneg hδ₀ hL)
  nlinarith

end Submission.Obl.k4_clean_cover_graph_atlas
