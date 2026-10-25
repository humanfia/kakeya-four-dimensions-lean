/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldResidualScale.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldResidualLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

/-- Primitive ORIGINAL floors and caps at one selected resolution. These
are all established before residual common choice. No list bound or
pairwise residual comparison is a field of this record. -/
structure OriginalResidualScale
    (μ : Measure ScalarIncidence) (θ : Measure ScalarLine) (π : Measure ℝ)
    (R E : Set ScalarIncidence) (ρ b r H : ℝ) (q : Fin 5 → ℤ) where
  β : ℝ
  A : ℝ
  η : ℝ
  C : ℝ
  s : ℝ
  ηp : ℝ
  Cg : ℝ
  beta_pos : 0 < β
  scale : β ≤ ρ * r
  A_pos : 0 < A
  eta_pos : 0 < η
  C_nonneg : 0 ≤ C
  s_pos : 0 < s
  etap_pos : 0 < ηp
  Cg_nonneg : 0 ≤ Cg
  palette : π (scalarVelocityBin ρ (q 1)) ≠ 0
  old : (Fin 3 → ℤ) → ℝ≥0∞
  graph_cap : ∀ (W : Fin 3 → ℤ) (j : ℤ),
    μ {p | cell b (scalarPosition p) = W ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j} ≤
      ENNReal.ofReal Cg * old W * π (scalarVelocityBin β j)
  posterior_floor : ∀ a : OriginalPosteriorRecord,
    R ∩ (posteriorEntryRecord ρ b r ⁻¹' {a}) = ∅ ∨
      ENNReal.ofReal ηp * old a.2.1 * π (scalarVelocityBin ρ a.2.2) <
        μ (R ∩ (posteriorEntryRecord ρ b r ⁻¹' {a}))
  coefficient_floor : ∀ (z : Fin 3 → ℤ) (B : Fin 5 → ℤ),
    R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z = ∅ ∨
      ENNReal.ofReal (r / A) * θ (parameterPiece ρ β q B) <
        μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z)
  prior_floor : ∀ (z : Fin 3 → ℤ) (j : ℤ) (B : Fin 5 → ℤ),
    μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z) ≠ 0 →
    B 1 = j → ENNReal.ofReal (η * s / H) * π (scalarVelocityBin β j) ≤
      θ (parameterPiece ρ β q B)
  cell_cap : ∀ (z : Fin 3 → ℤ) (j : ℤ),
    μ {p | p ∈ E ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j ∧ cell r (position ρ q p) = z} ≤
      ENNReal.ofReal (H ^ 2 * r * C * s) * π (scalarVelocityBin β j)

noncomputable section

def OriginalResidualScale.listBound
    {μ : Measure ScalarIncidence} {θ : Measure ScalarLine} {π : Measure ℝ}
    {R E : Set ScalarIncidence} {ρ b r H : ℝ} {q : Fin 5 → ℤ}
    (raw : OriginalResidualScale μ θ π R E ρ b r H q) (Hrow L : ℝ) : ℝ :=
  (raw.Cg / raw.ηp + 2) *
    ((raw.A * H ^ 3 * raw.C / raw.η) * (2 * (7 + Hrow + 2 * L) + 2))

/-- A primitive scale certificate yields all of its actual canonical
cellwise lists. In particular the list count is DERIVED from the original
floors, and contains no interpolation factor from the second grid. -/
theorem OriginalResidualScale.lists
    {μ : Measure ScalarIncidence} [IsFiniteMeasure μ]
    {θ : Measure ScalarLine} {π : Measure ℝ} [IsFiniteMeasure π]
    {R E : Set ScalarIncidence} {ρ b r H : ℝ} {q : Fin 5 → ℤ}
    (raw : OriginalResidualScale μ θ π R E ρ b r H q)
    (hR : MeasurableSet R) (hRE : R ⊆ E)
    (hρ : 0 < ρ) (hb : 0 < b) (hr : 0 < r) (hH : 1 ≤ H)
    (hcoeff : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H) (htime : ∀ p ∈ R, |p.2| ≤ 1)
    (F : ℝ → ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    {Hrow L ζ δ ε Hc : ℝ} (hHrow : 0 ≤ Hrow) (hL : 0 ≤ L)
    (hζr : ζ ≤ r) (hprecision : δ + ε / ρ + 2 * Hc * b / ρ ≤ ζ)
    (hcenter : |(center ρ q).2 4| ≤ Hc)
    (hrow : ∀ p ∈ R, cell ρ p.1.2 = q → |F p.2| ≤ Hrow)
    (hrowvar : ∀ p ∈ R, cell ρ p.1.2 = q → ∀ p' ∈ R, cell ρ p'.1.2 = q →
      |F p.2 - F p'.2| ≤ L * (|p.2 - p'.2| + ζ))
    (hrowclose : ∀ p ∈ R, cell ρ p.1.2 = q →
      |G (cell b (scalarPosition p)) 1 - F p.2| ≤ δ)
    (hgraph : ∀ p ∈ R,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
        G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε) :
    ∀ z : Fin 3 → ℤ, ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ raw.listBound Hrow L ∧
      ∀ p ∈ R, cell ρ p.1.2 = q → cell r (position ρ q p) = z →
        ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / r⌋ ∈ Q := by
  intro z
  exact canonical_residual_list_of_original_floors μ θ π hR hRE hρ raw.beta_pos hb hr
    raw.scale raw.A_pos hH raw.eta_pos raw.C_nonneg raw.s_pos raw.etap_pos raw.Cg_nonneg
    hHrow hL hζr hprecision q z raw.palette raw.old raw.graph_cap raw.posterior_floor
    hcoeff htime (raw.coefficient_floor z) (raw.prior_floor z) (raw.cell_cap z)
    F G hcenter hrow hrowvar hrowclose hgraph

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
