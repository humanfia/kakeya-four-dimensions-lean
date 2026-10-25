/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarGridCovering.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarCovering

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

/-- Only the selected finite scale list needs geometric estimates. -/
structure ScalarScaleRounding (ζ Q : ℝ) (grid : Set ℝ) : Prop where
  finer : ∀ r, ζ ≤ r → r ≤ 1 → ∃ s ∈ grid, 0 < s ∧ s ≤ r ∧ r ≤ Q * s
  coarser : ∀ r, ζ ≤ r → r ≤ 1 → ∃ s ∈ grid, r ≤ s ∧ s ≤ 1 ∧ s ≤ Q * r

structure ScalarGridCovers (grid : Set ℝ) (d K : ℝ) (S : Set ℝ) : Prop where
  local_cover : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ a,
    ∃ (m : ℕ) (c : Fin m → ℝ), S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ K * (R / r) ^ d
  global_cover : ∀ r ∈ grid, 0 < r → r ≤ 1 →
    ∃ (m : ℕ) (c : Fin m → ℝ), S ⊆ ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ K * (1 / r) ^ d

/-- Interpolation costs two scale-rounding factors and is valid at every
real scale in the exact higher-jet `IntervalAD` interface. -/
theorem intervalAD_of_scale_rounding {ζ Q d K : ℝ} {grid S : Set ℝ}
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hQ : 1 ≤ Q) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hround : ScalarScaleRounding ζ Q grid) (hgrid : ScalarGridCovers grid d K S) :
    IntervalAD ζ d (K * (Q ^ 2) ^ d) S := by
  have hQ₀ : 0 ≤ Q := by linarith
  have hQQ : Q ≤ Q ^ 2 := by nlinarith
  have hconstant : 0 ≤ K * (Q ^ 2) ^ d := by positivity
  have hglobal (r : ℝ) (hζr : ζ ≤ r) (hr₁ : r ≤ 1) :
      ∃ (m : ℕ) (c : Fin m → ℝ), S ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ (K * (Q ^ 2) ^ d) * (1 / r) ^ d := by
    have hr : 0 < r := hζ.trans_le hζr
    obtain ⟨s, hsg, hs, hsr, hrs⟩ := hround.finer r hζr hr₁
    obtain ⟨m, c, hcover, hcard⟩ := hgrid.global_cover s hsg hs (hsr.trans hr₁)
    refine ⟨m, c, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨j, mem_closedBall.mpr ((mem_closedBall.mp hj).trans hsr)⟩
    · have hinv : 1 / s ≤ Q / r := (div_le_div_iff₀ hs hr).mpr (by simpa only [one_mul] using hrs)
      have hratio : 1 / s ≤ Q ^ 2 * (1 / r) := hinv.trans
        ((div_le_div_of_nonneg_right hQQ hr.le).trans_eq (by ring))
      calc
        _ ≤ K * (1 / s) ^ d := hcard
        _ ≤ K * (Q ^ 2 * (1 / r)) ^ d := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hratio hd) hK
        _ = _ := by rw [Real.mul_rpow (sq_nonneg Q) (by positivity : 0 ≤ 1 / r)]; ring
  intro r R a hζr hrR
  have hr : 0 < r := hζ.trans_le hζr
  by_cases hr₁ : r ≤ 1
  · by_cases hR₁ : R ≤ 1
    · obtain ⟨s, hsg, hs, hsr, hrs⟩ := hround.finer r hζr hr₁
      obtain ⟨T, hTg, hRT, _, hTR⟩ := hround.coarser R (hζr.trans hrR) hR₁
      obtain ⟨m, c, hcover, hcard⟩ := hgrid.local_cover s hsg T hTg hs (hsr.trans (hrR.trans hRT)) a
      refine ⟨m, c, ?_, ?_⟩
      · intro x hx
        have hxT : x ∈ S ∩ Icc a (a + T) := ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hxT)
        exact mem_iUnion.mpr ⟨j, mem_closedBall.mpr ((mem_closedBall.mp hj).trans hsr)⟩
      · have hinv : 1 / s ≤ Q / r := (div_le_div_iff₀ hs hr).mpr (by simpa only [one_mul] using hrs)
        have hR : 0 < R := hr.trans_le hrR
        have hT : 0 < T := hR.trans_le hRT
        have hratio : T / s ≤ Q ^ 2 * (R / r) := by
          calc
            T / s = T * (1 / s) := by ring
            _ ≤ (Q * R) * (Q / r) := mul_le_mul hTR hinv (by positivity) (by positivity)
            _ = _ := by ring
        calc
          _ ≤ K * (T / s) ^ d := hcard
          _ ≤ K * (Q ^ 2 * (R / r)) ^ d := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hratio hd) hK
          _ = _ := by rw [Real.mul_rpow (sq_nonneg Q) (by positivity : 0 ≤ R / r)]; ring
    · obtain ⟨m, c, hcover, hcard⟩ := hglobal r hζr hr₁
      refine ⟨m, c, inter_subset_left.trans hcover, ?_⟩
      exact hcard.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_right (by linarith : 1 ≤ R) hr.le) hd) hconstant)
  · obtain ⟨m, c, hcover, hcard⟩ := hglobal 1 hζ₁ le_rfl
    refine ⟨m, c, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx.1)
      exact mem_iUnion.mpr ⟨j, mem_closedBall.mpr ((mem_closedBall.mp hj).trans (by linarith))⟩
    · have hcard' : (m : ℝ) ≤ K * (Q ^ 2) ^ d := by simpa only [div_one, Real.one_rpow, mul_one] using hcard
      have hratio : 1 ≤ R / r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hrR)
      exact hcard'.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.one_le_rpow hratio hd) hconstant)

end Submission.Obl.k4_scalar_graph_residual_discovery
