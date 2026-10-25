/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueNormalization.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NormalizedProfileZero

/-! Actual chosen true-atlas provenance, packaged with the literal
refinement that survives pure homogenization and exact completion. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

/-- The true source atlas and its injected, incidence-restricted
normalization are both retained. Its full prior is never restricted to
the selected incidences. -/
structure TrueNormalization (p q : Code) (r b h : ℝ) where
  parent_exact : Exact p
  atlas : TrueChosenCharts p r b h
  countExponent : ℕ
  degreeBound : ℕ
  cap : ℝ
  retained : RetainedRefinement (chosen_refinement_witness atlas.toChosenCharts
    (specExact_of_exact parent_exact).1 countExponent degreeBound cap)
  code_eq : retained.code = q

namespace TrueNormalization

variable {p q : Code} {r b h : ℝ}

/-- The literal witness of this very normalization. -/
def witness (a : TrueNormalization p q r b h) : RefinementWitness p q r b h := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  exact out.witness

/-- The vanishing floor loss follows the same strict retained sample map. -/
def floorLoss (a : TrueNormalization p q r b h) : ℕ → ℝ :=
  a.atlas.ε ∘ a.retained.sample

theorem floorLoss_tendsto (a : TrueNormalization p q r b h) :
    Tendsto a.floorLoss atTop (nhds 0) :=
  a.atlas.ε_lim.comp a.retained.sample_strictMono.tendsto_atTop

theorem saturated (a : TrueNormalization p q r b h) :
    a.witness.toRefinementData.Saturated r a.floorLoss := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  exact out.saturation atlas.ε (chosen_true_saturation atlas hp M' D' d')

theorem profile_zero (a : TrueNormalization p q r b h) (hq : Exact q)
    (hLq : L q = L p - r) (hr : 0 ≤ r) : f q 0 = 0 :=
  a.witness.profile_zero_eq_of_saturation a.parent_exact hq hLq hr
    a.floorLoss a.floorLoss_tendsto a.saturated

end TrueNormalization

/-- True normalization at the very supplied source depth and cost.
In addition to the usual calculus conclusions, the true atlas and all
original full assignments remain linked to the exact output. -/
theorem exists_true_normalization {p : Code} {r b h d' : ℝ}
    (hp : Exact p) (hk : TrueKnown p r b h)
    (hr : 0 ≤ r) (hrL : r < L p) (hrb : r ≤ b) (hbL : b ≤ L p)
    (hd' : 0 ≤ d') (hd'1 : d' < 1)
    (htail : ∀ s, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d' * (L p - s)) :
    ∃ q : Code, Nonempty (TrueNormalization p q r b h) ∧
      Exact q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * (L p - r) / L p ∧ Horizon p ≤ h + Horizon q ∧
      (∀ s, 0 ≤ s → s ≤ L q →
        f q (L q) - f q s ≤ f p (L p) - f p (r + s)) ∧
      (b = r → ∀ s, 0 ≤ s → s ≤ L q →
        f q s - f q 0 = f p (r + s) - f p r) ∧ f q 0 = 0 := by
  obtain ⟨a⟩ := nonempty_true_chosen_charts hp hk
  obtain ⟨M', D', out, hq, hL, hd, hS, hU, hH, hrel, heq⟩ :=
    normalize_through_chosen_charts hp a.toChosenCharts hr hrL hrb hbL hk.1 hd' hd'1 htail
  let cert : TrueNormalization p out.code r b h := ⟨hp, a, M', D', d', out, rfl⟩
  exact ⟨out.code, ⟨cert⟩, hq, hL, hd, hS, hU, hH, hrel, heq,
    cert.profile_zero hq hL hr⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
