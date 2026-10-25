/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ComparisonMesh.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetCellJitter

/-!
# A finite comparison mesh of the actual source law

The pieces are literal restrictions of the original law by its measurable cell code.
The normalized uniform cell laws and all pair-law operations are derived from those
pieces. No replacement source law or representative pair is introduced.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

structure ComparisonMesh {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  n : ℕ
  code : Ω → Fin n
  measurable_code : Measurable code
  base : Ω → EuclideanSpace ℝ (Fin 3)
  measurable_base : Measurable base
  cell : Fin n → Set (EuclideanSpace ℝ (Fin 3))
  measurable_cell : ∀ q, MeasurableSet (cell q)
  disjoint_cell : Pairwise (fun q q' => Disjoint (cell q) (cell q'))
  vol : ℝ≥0∞
  vol_ne_zero : vol ≠ 0
  vol_ne_top : vol ≠ ⊤
  cell_volume : ∀ q, volume (cell q) = vol
  diameter : ℝ
  diameter_le : diameter ≤ 1 / 8
  dist_le : ∀ q, ∀ x ∈ cell q, ∀ y ∈ cell q, dist x y ≤ diameter
  original : ∀ᵐ p ∂μ, ‖base p‖ ≤ 1 / 8 ∧ base p ∈ cell (code p)

namespace ComparisonMesh

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : ComparisonMesh μ)

/-- A later restriction uses exactly the same original finite cells and code. -/
def mono {ν : Measure Ω} (hν : ν ≤ μ) : ComparisonMesh ν :=
  { n := M.n
    code := M.code
    measurable_code := M.measurable_code
    base := M.base
    measurable_base := M.measurable_base
    cell := M.cell
    measurable_cell := M.measurable_cell
    disjoint_cell := M.disjoint_cell
    vol := M.vol
    vol_ne_zero := M.vol_ne_zero
    vol_ne_top := M.vol_ne_top
    cell_volume := M.cell_volume
    diameter := M.diameter
    diameter_le := M.diameter_le
    dist_le := M.dist_le
    original := M.original.filter_mono (ae_mono hν) }

def pieces : Fin M.n → Measure Ω := codePieces μ M.code

def cellLaws : Fin M.n → Measure (EuclideanSpace ℝ (Fin 3)) :=
  fun q => uniformCellLaw volume (M.cell q) M.vol

local instance pieces_finite [IsFiniteMeasure μ] (q : Fin M.n) : IsFiniteMeasure (M.pieces q) := by
  dsimp [pieces, codePieces]
  infer_instance

local instance cellLaws_probability (q : Fin M.n) : IsProbabilityMeasure (M.cellLaws q) :=
  uniformCellLaw_probability volume (M.cell q) M.vol M.vol_ne_zero M.vol_ne_top (M.cell_volume q)

theorem pieces_sum : (∑ q, M.pieces q) = μ :=
  codePieces_sum μ M.code M.measurable_code

theorem cellLaws_cap (q : Fin M.n) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    M.cellLaws q U ≤ M.vol⁻¹ * volume (U ∩ M.cell q) :=
  uniformCellLaw_cap volume (M.cell q) M.vol U hU

theorem cellLaws_support (q : Fin M.n) : ∀ᵐ y ∂M.cellLaws q, y ∈ M.cell q :=
  uniformCellLaw_support volume (M.cell q) M.vol (M.measurable_cell q)

/-- A primitive original index-cell cap is exactly the cap of the corresponding piece. -/
theorem pieces_index_cap {n : ℕ} (index : Ω → Fin n) (hi : Measurable index) (i : Fin n)
    (A : ℝ≥0∞)
    (hcap : ∀ q, μ {p | M.code p = q ∧ index p = i} ≤ A * M.vol) :
    ∀ q, M.pieces q {p | index p = i} ≤ A * M.vol := by
  intro q
  have hmeas : MeasurableSet {p | index p = i} := hi (measurableSet_singleton i)
  rw [pieces, codePieces, Measure.restrict_apply hmeas]
  have heq : {p | index p = i} ∩ {p | M.code p = q} = {p | M.code p = q ∧ index p = i} := by
    ext p
    exact and_comm
  rw [heq]
  exact hcap q

/-- Resolved cells preserve agreement of the original labeled sheets. -/
theorem cell_agreement {n₁ n₂ : ℕ} (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (f₁ : Fin n₁ → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℝ (Fin 3) → ℂ) (K : NNReal) {a : ℝ}
    (hsmall : 2 * (K : ℝ) * M.diameter ≤ a / 2)
    (hlip₁ : ∀ i, LipschitzOnWith K (f₁ i) (closedBall 0 (1 / 2)))
    (hlip₂ : ∀ j, LipschitzOnWith K (f₂ j) (closedBall 0 (1 / 2)))
    (hsource : ∀ᵐ p ∂μ, ‖f₁ (i₁ p) (M.base p) - f₂ (i₂ p) (M.base p)‖ ≤ a / 2) :
    ∀ q, ∀ᵐ p ∂M.pieces q, ∀ y ∈ M.cell q,
      ‖y‖ ≤ 1 / 4 ∧ ‖f₁ (i₁ p) y - f₂ (i₂ p) y‖ ≤ a := by
  intro q
  filter_upwards [ae_restrict_mem (M.measurable_code (measurableSet_singleton q)),
    M.original.filter_mono (ae_mono Measure.restrict_le_self),
    hsource.filter_mono (ae_mono Measure.restrict_le_self)] with p hq hp hfit
  intro y hy
  have hbase : M.base p ∈ M.cell q := by simpa only [hq] using hp.2
  exact sheet_close_on_cell (f₁ (i₁ p)) (f₂ (i₂ p)) K M.diameter_le hsmall
    (hlip₁ _) (hlip₂ _) hp.1 (M.dist_le q y hy (M.base p) hbase) hfit

/-- The actual pair law with the resampled common base point. -/
def pairedLaw {n₁ n₂ : ℕ} (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) :
    Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3)) :=
  meshPairLaw M.pieces M.cellLaws i₁ i₂

theorem pairedLaw_index_mass [IsFiniteMeasure μ] {n₁ n₂ : ℕ}
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) (hi₁ : Measurable i₁) (hi₂ : Measurable i₂)
    (E : Set (Fin n₁ × Fin n₂)) :
    M.pairedLaw i₁ i₂ {p | p.1 ∈ E} = μ {p | (i₁ p, i₂ p) ∈ E} := by
  rw [pairedLaw, meshPairLaw_index_mass M.pieces M.cellLaws i₁ i₂ hi₁ hi₂ E, M.pieces_sum]

end ComparisonMesh

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
