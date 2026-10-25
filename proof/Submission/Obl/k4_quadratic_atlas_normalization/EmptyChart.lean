import Submission.Obl.k4_quadratic_atlas_normalization.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

/-!
# Charts without assigned trajectories

A rough chart's frame (`Q`, `c`, `u`) and test `R` give a known chart with empty assignment and
selection, at any depth, larger format exponent and larger slack. Both curvature steps use it
for the charts of the other curvature case.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set

/-- A chart without assigned trajectories, keeping a rough chart's frame and test. -/
theorem chart_empty_of_rough {N κ κ' j L a r B : ℝ} {M M' D T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hκκ' : κ ≤ κ')
    (h : rough N M D κ T j L a B E c u Q R A F ex) (hex' : ex') :
    chart N M' D κ' T j r B E c u Q R ∅ ∅ ex' := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  have hH : (0 : ℝ) ≤ N ^ M' := pow_nonneg (zero_le_one.trans hN) _
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF,
    hformat, hwhole, hselected, hdisc, hext⟩
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow,
    hsize.trans (div_le_div_of_nonneg_right hκκ' (by positivity)), hdeg,
    fun e => (hcoeff e).trans hpow, MeasurableSet.empty, MeasurableSet.empty,
    fun i => ⟨?_, ?_⟩, fun l hl => absurd hl (notMem_empty l),
    fun p hp => absurd hp (notMem_empty p), hex'⟩
  · simpa using fmt_empty 6 D hH
  · simpa using fmt_empty 7 D hH

end Submission.Obl.k4_quadratic_atlas_normalization
