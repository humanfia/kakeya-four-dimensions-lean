-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/ChartMonotonicity.lean
import Submission.Obl.k4_terminal_label_saturation.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_terminal_label_saturation

open Set

/-- Enlarging the polynomial format and the common subpower slack preserves
all chart conditions, including the selected-incidence derivative floor. -/
theorem chart_mono
    {N κ κ' j r B : ℝ} {M M' D D' T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hD : D ≤ D')
    (hκ : 0 < κ) (hκκ' : κ ≤ κ') (hB : 0 ≤ B)
    (h : chart N M D κ T j r B E c u Q R A F ex) (hex : ex → ex') :
    chart N M' D' κ' T j r B E c u Q R A F ex' := by
  exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
    hN hM hD hκ hκκ' hB h hex

end Submission.Obl.k4_terminal_label_saturation
