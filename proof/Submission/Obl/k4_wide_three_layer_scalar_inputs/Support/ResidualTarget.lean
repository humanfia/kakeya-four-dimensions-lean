import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Sigma
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Caps

set_option linter.unusedVariables false

/-!
# The residual support step (statement only)

After the common field `C` has been applied, the corrected residual
`resid - (C₀ + C₁ zt + C₂ zZ) tr - C₃ tr²` of an incidence equals its coarse base quadratic plus
its layer-2 offset, to the layer-2 precision.  With the per-chart lists of coarse predictors and
of layer-2 offsets, and the conditional velocity domination of output states supplied by the
nested deep atlas blocks, a restriction of the law has a finite residual support table of the
frozen size.  `ResidualSupportAt` is the per-index statement used by the assembly.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- The frozen output bins of an incidence: normalized base cell at `σ = N^-m` and corrected
residual bin at `N^-v`. -/
def outBins (F : Frame) (C : Fin 4 → ℝ) (σ τv : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    (Fin 2 → ℤ) × ℤ :=
  (![⌊F.zt t / σ⌋, ⌊F.zZ b t / σ⌋],
    ⌊(F.resid b t - transv C (F.zt t) (F.zZ b t) (F.tr b t)) / τv⌋)

/-- **The residual support statement at one index** (to be proved; the assembly uses it).

Data: the coarse block `i` (frame `F`, affine graph `L`), a deep depth `se` whose atlas blocks are
nested in depth-`s` blocks, a law `θ ≤ μ` on the block, the common field `C`, the compared labels
(coarse predictors `γ` on charts `chartOf γ`, base quadratics `pc`, layer-2 offsets `D2`) with the
corrected layer-2 fit `fitC` and the per-chart lists.  The numeric hypotheses say that on a deep
block the base coordinates vary by at most `σ = N^-m` and the corrected residual by at most
`τv = N^-v`, and that the charts met in one base cell with one fine velocity bin are at most `M₀`.

Conclusion: a restriction `θ'` losing at most `δp · 27 · q ν(A_i)` carries a finite table of
(base cell, corrected residual bin) of size `(N^m+2)(2 Kz N^m+2) · (K/δp) · M₀ H³ N^{dv} · 7`. -/
def ResidualSupportAt {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (s se R v' : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (θ : Measure (α × ℝ)) (C : Fin 4 → ℝ)
    (Γ Λ : Type) [Fintype Γ] [Fintype Λ] (lab : α → Λ) (crs : Λ → Γ) (chartOf : Γ → ℤ × ℤ)
    (pc : Γ → Fin 6 → ℝ) (D2 : Λ → ℝ) (χ H m v Kz M₀ : ℝ) (δp : ℝ≥0∞) : Prop :=
  let F := blockFrame cfg k s i L
  let σ := cfg.N k ^ (-m)
  let τv := cfg.N k ^ (-v)
  -- hypotheses
  (∀ x, MeasurableSet (lab ⁻¹' {x})) →
  θ ≤ cfg.μ k →
  (∀ᵐ p ∂θ, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)) →
  (∀ᵐ p ∂θ, |F.zZ (cfg.b k p.1) p.2| ≤ Kz) →
  (∀ γ e, |pc γ e| ≤ H) →
  (∀ᵐ p ∂θ, (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) = chartOf (crs (lab p.1))) →
  (∀ᵐ p ∂θ, |F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
      (F.tr (cfg.b k p.1) p.2) - quadZ (pc (crs (lab p.1))) (F.zt p.2) (F.zZ (cfg.b k p.1) p.2) -
      D2 (lab p.1)| ≤ H * τv) →
  (∀ ch : ℤ × ℤ, ∃ G : Finset Γ, (G.card : ℝ) ≤ H ∧
    ∀ᵐ p ∂θ, (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) = ch → crs (lab p.1) ∈ G) →
  (∀ (ch : ℤ × ℤ) (γ : Γ), ∃ Fo : Finset ℤ, (Fo.card : ℝ) ≤ H * cfg.N k ^ (cfg.d * v) ∧
    ∀ᵐ p ∂θ, (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) = ch → crs (lab p.1) = γ →
      ⌊D2 (lab p.1) / τv⌋ ∈ Fo) →
  -- deep blocks: the output coordinates vary by at most one bin on each deep block
  (∀ j : Fin (cfg.n k se), ∃ h : Fin (cfg.n k s), cfg.A k se j ⊆ cfg.A k s h ∧
    Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h)) →
  (∀ j : Fin (cfg.n k se), ∀ p ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
      (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)),
    ∀ p' ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
      (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)),
    |F.zt p.2 - F.zt p'.2| ≤ σ ∧ |F.zZ (cfg.b k p.1) p.2 - F.zZ (cfg.b k p'.1) p'.2| ≤ σ ∧
    |(F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
        (F.tr (cfg.b k p.1) p.2)) -
      (F.resid (cfg.b k p'.1) p'.2 - transv C (F.zt p'.2) (F.zZ (cfg.b k p'.1) p'.2)
        (F.tr (cfg.b k p'.1) p'.2))| ≤ τv) →
  -- the charts met in one base cell with one fine velocity bin
  (∀ (z : Fin 2 → ℤ) (w : ℤ), ∃ Ch : Finset (ℤ × ℤ), (Ch.card : ℝ) ≤ M₀ ∧
    ∀ᵐ p ∂θ, ![⌊F.zt p.2 / σ⌋, ⌊F.zZ (cfg.b k p.1) p.2 / σ⌋] = z →
      vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) = w →
        (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋) ∈ Ch) →
  -- the base quadratics vary by at most one residual bin on a base cell
  H * (5 + 3 * Kz) * σ ≤ τv →
  δp ≠ 0 → δp ≠ ⊤ →
  -- conclusion
  ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
    θ univ ≤ θ' univ + δp * (((27 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i))) ∧
    ∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
      (Fs.card : ℝ) ≤ (cfg.N k ^ m + 2) * (2 * Kz * cfg.N k ^ m + 2) *
        ((ENNReal.ofReal (cfg.K k) / δp).toReal * M₀ * H ^ 3 * cfg.N k ^ (cfg.d * v) * 7) ∧
      ∀ᵐ p ∂θ', outBins F C σ τv (cfg.b k p.1) p.2 ∈ Fs

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
