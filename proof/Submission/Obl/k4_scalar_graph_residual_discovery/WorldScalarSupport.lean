/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldScalarSupport.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldStripSupport
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarGridGlobal

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Metric
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- Concrete global filling yields the FULL all-scale `SS` field in a
later coefficient world. Hereditary counts and filling refer to the
global final law; scalar witnesses and the row refer only to the selected
world. Every further subset of that world is permitted. -/
theorem world_scalar_support_of_global_filling
    {ρ b ζ Q d δ A B K H : ℝ}
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hQ : 1 ≤ Q) (hd : 0 ≤ d)
    (hK : 0 < K) (hH : 0 ≤ H)
    (grid : Set ℝ) (hunit : (1 : ℝ) ∈ grid)
    (hgrid : ∀ r ∈ grid, ζ ≤ r ∧ r ≤ 1)
    (hround : ScalarScaleRounding ζ Q grid)
    (q : Fin 5 → ℤ) (E Eall : Set ScalarIncidence) (hsub : E ⊆ Eall)
    (F : ℝ → ℝ) (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ z ∈ E, cell ρ z.1.2 = q)
    (hfinite : ((fun z => cell b (scalarPosition z)) '' E).Finite)
    (htime : ∀ z ∈ E, |z.2| ≤ 1)
    (hF : ∀ z ∈ E, |F z.2| ≤ H)
    (hrow : ∀ z ∈ E, |row (assignedCell ρ b z) 1 - F z.2| ≤ δ)
    (hprecision : ∀ v, 2 * δ + (1 + |row v 0| + |row v 1|) * b / ρ ≤ ζ)
    (hA : ∀ v, 5 + |row v 0| + |row v 1| ≤ A)
    (hereditary : ℝ → ℝ → (Fin 3 → ℤ) → Finset (Fin 3 → ℤ))
    (hcount : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ v,
      ((hereditary r R v).card : ℝ) ≤ B * (R / r) ^ ((2 : ℝ) + d))
    (hmem : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ z ∈ Eall,
      cell (ρ * r) (assignedPosition b z) ∈
        hereditary r R (cell (ρ * R) (assignedPosition b z)))
    (hbudget : 18 * (A + 1) * B ≤ K) (hoverlap : 2 * A + 2 ≤ K)
    (hfill : ∀ r ∈ grid, ∀ v j,
      (∃ z ∈ Eall, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j) →
        (ρ / (ρ * r)) ^ 2 / K ≤
          ((normalStripPhysicalCells (assignedPosition b) {z ∈ Eall | assignedCell ρ b z = v}
            (row v) (ρ * r) j).ncard : ℝ)) :
    ∀ t, IntervalAD ζ d
      (((4 * (3 + 2 * H) + 3) * (10648 * K ^ 3)) * (Q ^ 2) ^ d)
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ Zoom.scalar ρ q F l t = s} := by
  intro t
  let S := {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ Zoom.scalar ρ q F l t = s}
  have hbound : ∀ s ∈ S, |s| ≤ 3 + 2 * H := by
    rintro _ ⟨l, hl, rfl⟩
    exact Zoom.abs_scalar_le hρ (hworld (l, t) hl) (htime (l, t) hl) (hF (l, t) hl)
  have hlocal : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ a,
      ∃ (m : ℕ) (c : Fin m → ℝ), S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ (10648 * K ^ 3) * (R / r) ^ d := by
    intro r hr R hR hr₀ hrR a
    have hR₀ : 0 < R := hr₀.trans_le hrR
    by_cases ht : |t| ≤ 1
    · have hbudget' : 18 * (A + 1) * (B * (R / r) ^ ((2 : ℝ) + d)) ≤
          K * (R / r) ^ ((2 : ℝ) + d) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbudget
          (Real.rpow_nonneg (div_nonneg hR₀.le hr₀.le) ((2 : ℝ) + d))
      exact scalar_local_cover_of_global_strip_filling hρ hb hbρ hr₀ hrR (hgrid R hR).2 hK ht
        q E Eall hsub F row hworld hfinite hrow
        (fun v => (hprecision v).trans (hgrid r hr).1) hA (hereditary r R)
        (hcount r hr R hR hr₀ hrR) (hmem r hr R hR hr₀ hrR) hbudget' hoverlap (hfill r hr)
    · refine ⟨0, Fin.elim0, ?_, ?_⟩
      · rintro s ⟨⟨l, hl, _⟩, _⟩
        exact False.elim (ht (htime (l, t) hl))
      · norm_num only [Nat.cast_zero]
        positivity
  have hcover := scalar_grid_covers_of_bounded (by positivity : 0 ≤ 10648 * K ^ 3)
    (by positivity : 0 ≤ 3 + 2 * H) hunit hbound hlocal
  exact intervalAD_of_scale_rounding hζ hζ₁ hQ hd (by positivity) hround hcover

end

end Submission.Obl.k4_scalar_graph_residual_discovery
