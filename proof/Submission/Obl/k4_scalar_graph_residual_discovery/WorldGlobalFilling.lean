/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldGlobalFilling.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldScalarSupport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

namespace Zoom

/-- Whole GLOBAL assigned-strip filling and hereditary physical lists.
The global set remains fixed when a later coefficient world is restricted. -/
structure GlobalWorldFilling (R : Set ScalarIncidence) (ρ b ζ d : ℝ) where
  Q : ℝ
  K : ℝ
  A : ℝ
  B : ℝ
  one_le_Q : 1 ≤ Q
  K_pos : 0 < K
  grid : Set ℝ
  unit : (1 : ℝ) ∈ grid
  grid_bounds : ∀ r ∈ grid, ζ ≤ r ∧ r ≤ 1
  rounding : ScalarScaleRounding ζ Q grid
  row : (Fin 3 → ℤ) → Fin 2 → ℝ
  row_bound : ∀ v, 5 + |row v 0| + |row v 1| ≤ A
  hereditary : ℝ → ℝ → (Fin 3 → ℤ) → Finset (Fin 3 → ℤ)
  count : ∀ r ∈ grid, ∀ r' ∈ grid, 0 < r → r ≤ r' → ∀ v,
    ((hereditary r r' v).card : ℝ) ≤ B * (r' / r) ^ ((2 : ℝ) + d)
  mem : ∀ r ∈ grid, ∀ r' ∈ grid, 0 < r → r ≤ r' → ∀ z ∈ R,
    cell (ρ * r) (assignedPosition b z) ∈
      hereditary r r' (cell (ρ * r') (assignedPosition b z))
  budget : 18 * (A + 1) * B ≤ K
  overlap : 2 * A + 2 ≤ K
  filling : ∀ r ∈ grid, ∀ v j,
    (∃ z ∈ R, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j) →
      (ρ / (ρ * r)) ^ 2 / K ≤
        ((normalStripPhysicalCells (assignedPosition b) {z ∈ R | assignedCell ρ b z = v}
          (row v) (ρ * r) j).ncard : ℝ)

noncomputable section

def GlobalWorldFilling.supportBound {R : Set ScalarIncidence} {ρ b ζ d : ℝ}
    (raw : GlobalWorldFilling R ρ b ζ d) (Hrow : ℝ) : ℝ :=
  ((4 * (3 + 2 * Hrow) + 3) * (10648 * raw.K ^ 3)) * (raw.Q ^ 2) ^ d

/-- Actual global filling gives the scalar support field on ANY later
subset of a coefficient world. Filling is never asserted inside that tiny
world, and no intersection of independently selected fits is used. -/
theorem GlobalWorldFilling.support_on_world_subset
    {R : Set ScalarIncidence} {ρ b ζ d : ℝ} (raw : GlobalWorldFilling R ρ b ζ d)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hd : 0 ≤ d)
    (q : Fin 5 → ℤ) (E : Set ScalarIncidence) (hsub : E ⊆ R)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (hfinite : ((fun p => cell b (scalarPosition p)) '' E).Finite)
    (htime : ∀ p ∈ E, |p.2| ≤ 1)
    (F : ℝ → ℝ) {Hrow δ : ℝ} (hHrow : 0 ≤ Hrow)
    (hF : ∀ p ∈ E, |F p.2| ≤ Hrow)
    (hrow : ∀ p ∈ E, |raw.row (assignedCell ρ b p) 1 - F p.2| ≤ δ)
    (hprecision : ∀ v, 2 * δ + (1 + |raw.row v 0| + |raw.row v 1|) * b / ρ ≤ ζ) :
    ∀ t, IntervalAD ζ d (raw.supportBound Hrow)
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ scalar ρ q F l t = s} := by
  exact world_scalar_support_of_global_filling hρ hb hbρ hζ hζ₁ raw.one_le_Q hd
    raw.K_pos hHrow raw.grid raw.unit raw.grid_bounds raw.rounding q E R hsub F raw.row
    hworld hfinite htime hF hrow hprecision raw.row_bound raw.hereditary raw.count raw.mem
    raw.budget raw.overlap raw.filling

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
