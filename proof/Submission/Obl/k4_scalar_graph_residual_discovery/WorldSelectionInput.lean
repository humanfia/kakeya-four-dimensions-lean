/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldSelectionInput.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldResidualSelection

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

/-- Primitive input of residual world selection. The only list-related
field is an explicit NUMERICAL upper bound for the formula already proved
from original floors; there is no residual list or comparison oracle. -/
structure OriginalWorldSelectionInput
    (μ : Measure ScalarIncidence) (θ : Measure ScalarLine) (π : Measure ℝ)
    (R E : Set ScalarIncidence) (ρ b H Hc Krow Hrow A ζ ε : ℝ)
    (q : Fin 5 → ℤ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ) where
  measurable_R : MeasurableSet R
  sub : R ⊆ E
  rho_pos : 0 < ρ
  rho_le_one : ρ ≤ 1
  b_pos : 0 < b
  one_le_H : 1 ≤ H
  one_le_Hc : 1 ≤ Hc
  Krow_nonneg : 0 ≤ Krow
  Hrow_nonneg : 0 ≤ Hrow
  one_le_A : 1 ≤ A
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  rho_le_zeta : ρ ≤ ζ
  diameter_budget : (1 + 3 * Hc) * b / ρ ≤ ζ
  error_budget : 4 * worldRowConstant Hc Krow ^ 2 * ρ + ε / ρ + 2 * Hc * b / ρ ≤ ζ
  coeff_bound : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H
  time_mem : ∀ p ∈ R, p.2 ∈ Icc (0 : ℝ) 1
  center_bound : ∀ e, |(center ρ q).2 e| ≤ Hc
  row_bound : ∀ p ∈ R, cell ρ p.1.2 = q → |G (cell b (scalarPosition p)) 1| ≤ Hrow
  row_compare : ∀ p ∈ R, cell ρ p.1.2 = q → ∀ p' ∈ R, cell ρ p'.1.2 = q →
    |G (cell b (scalarPosition p)) 1 - G (cell b (scalarPosition p')) 1| ≤
      Krow * (‖scalarPosition p - scalarPosition p'‖ + ρ)
  graph_error : ∀ p ∈ R,
    |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
      G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε
  n : ℕ
  one_le_n : 1 ≤ n
  s : ℕ → ℝ
  K : ℕ → ℕ
  first_scale : s 0 = 1
  scale_pos : ∀ i, 0 < s i
  scale_floor : ∀ i < n, ζ ≤ s i
  ratio : ∀ i, i + 1 < n → s i ≤ A * s (i + 1)
  last_scale : s (n - 1) = ζ
  raw : (i : Fin n) → OriginalResidualScale μ θ π R E ρ b (s i) H q
  list_budget : ∀ i : Fin n,
    (raw i).listBound Hrow (12 * worldRowConstant Hc Krow ^ 2) ≤ (K i : ℝ)

/-- The raw input constructs the selected world and its comparison. -/
theorem OriginalWorldSelectionInput.select
    {μ : Measure ScalarIncidence} [IsFiniteMeasure μ] {θ : Measure ScalarLine}
    {π : Measure ℝ} [IsFiniteMeasure π] {R E : Set ScalarIncidence}
    {ρ b H Hc Krow Hrow A ζ ε : ℝ} {q : Fin 5 → ℤ} {G : (Fin 3 → ℤ) → Fin 2 → ℝ}
    (raw : OriginalWorldSelectionInput μ θ π R E ρ b H Hc Krow Hrow A ζ ε q G) :
    Nonempty (ResidualWorldSelection μ R ρ b q Hc Krow Hrow A ζ raw.n raw.K G) := by
  exact exists_residual_world_selection μ θ π raw.measurable_R raw.sub
    raw.rho_pos raw.rho_le_one raw.b_pos raw.one_le_H raw.one_le_Hc raw.Krow_nonneg
    raw.Hrow_nonneg raw.one_le_A raw.zeta_pos raw.zeta_le_one raw.rho_le_zeta
    raw.diameter_budget raw.error_budget q G raw.coeff_bound raw.time_mem raw.center_bound
    raw.row_bound raw.row_compare raw.graph_error raw.n raw.one_le_n raw.s raw.K
    raw.first_scale raw.scale_pos raw.scale_floor raw.ratio raw.last_scale raw.raw raw.list_budget

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
