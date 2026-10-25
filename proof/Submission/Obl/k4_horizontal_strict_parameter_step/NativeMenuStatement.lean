/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at c4765076c45bb6cb7fbc53c5859035579f22a4b1, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMenuStatement.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeOriginalDomains
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeProductStatement

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- The exact finite menus used by the original native time-block selector.
Only actual successful marked pairs with positive original palette and full
original witness floors occur. -/
def NativeMenuBound {α : Type} [MeasurableSpace α]
    {cfg : NativeModel α} {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)}
    (c : NativeComparisonData cfg k s σ) (M δ : ℝ) : Prop :=
  ∀ h : Fin c.m, ∀ block : Fin (2 ^ cfg.T k s),
    ({i : Fin (cfg.n k s) | c.paired M δ h i ∧ cfg.j k s i = block}.ncard : ℝ) ≤
      (100800 * cfg.K k * (M / c.a) ^ cfg.d) / δ

/-- The whole-domain counting adapter needed after actual matching. The
hypotheses are pointwise prepared data and actual product comparison, with no
assumed current pair floor or independent finite-list input. -/
def NativeOriginalMenuCounting : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : NativeModel α) (k : ℕ) (s : ℝ)
    (σ : Measure (α × ℝ)) (c : NativeComparisonData cfg k s σ),
    cfg.Basic → cfg.AssignmentLevel k s → cfg.μ k univ ≠ 0 →
    c.a = cfg.N k ^ (-s) → 0 ≤ cfg.d → cfg.d ≤ 1 →
    ∀ M δ : ℝ, c.A ≤ M → 2 * M ≤ 1 → 0 < δ →
      NativeProductComparison c M → NativeMenuBound c M δ

end

end Submission.Obl.k4_horizontal_strict_parameter_step
