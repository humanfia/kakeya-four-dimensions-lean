/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueAmbientCharts.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueAtlasSupport
import Submission.Obl.k4_scalar_normalized_exact_refinement.AtlasPruning
import Submission.Obl.k4_scalar_true_terminal_lifting.ChartMono

/-! The injected retained chart family still forms a TRUE source atlas
when its full original C pieces are kept. Its loss is the maximum of the
old true-chart loss and the new selected-coverage loss. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

namespace RetainedRefinement

/-- Restore full unchanged true pieces for the retained subfamily.
Accepted chart monotonicity and injective selection do the geometry;
the smaller selected C-prime supplies the union-mass lower bound. -/
theorem true_ambient_charts {p q : Code} {r b h : ℝ}
    {w : RefinementWitness p q r b h} (a : RetainedRefinement w) (hp : Exact p)
    (htrue : ∀ k, ChartData p w.exponent r b (h + w.loss k) (w.loss k) true
      (w.sample k) (w.T k) (W q k) (w.world k) (w.block k) (w.assignment k)
      (w.selected k) (w.center k) (w.speed k) (w.width k) (w.polynomial k) (w.lists k))
    (k : ℕ) :
    ChartData p (max w.exponent a.witness.exponent) r b
      (h + max (w.loss (a.sample k)) (a.witness.loss k))
      (max (w.loss (a.sample k)) (a.witness.loss k)) true
      (w.sample (a.sample k)) (w.T (a.sample k)) (W a.code k)
      (w.world (a.sample k) ∘ a.embedding k) (w.block (a.sample k) ∘ a.embedding k)
      (w.assignment (a.sample k) ∘ a.embedding k) (w.selected (a.sample k) ∘ a.embedding k)
      (w.center (a.sample k) ∘ a.embedding k) (w.speed (a.sample k) ∘ a.embedding k)
      (w.width (a.sample k) ∘ a.embedding k) (w.polynomial (a.sample k) ∘ a.embedding k)
      (restrictedChartList (a.embedding k) (w.lists (a.sample k))) := by
  have hN : 1 ≤ N p (w.sample (a.sample k)) := by linarith [hp.1.1 (w.sample (a.sample k))]
  have hmono := Submission.Obl.k4_scalar_true_terminal_lifting.chartData_mono
    (htrue (a.sample k)) hN (le_max_left w.exponent a.witness.exponent)
    (add_le_add le_rfl (le_max_left (w.loss (a.sample k)) (a.witness.loss k)))
    (le_max_left (w.loss (a.sample k)) (a.witness.loss k))
  apply chartData_restrict hmono (a.embedding k)
  have hmass := (a.witness.charts k).2
  rcases hmass with ⟨_, _, _, _, _, _, _, _, _, hmass⟩
  rw [a.data_eq] at hmass
  apply le_trans _ (hmass.trans ?_)
  · apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le hN
    change -max (w.loss (a.sample k)) (a.witness.loss k) ≤ -a.witness.loss k
    exact neg_le_neg (le_max_right _ _)
  · apply Finset.sum_le_sum
    intro g _
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro z ⟨i, hi, hz⟩
    exact ⟨i, hi, a.selected_subset k i hz⟩

end RetainedRefinement

namespace TrueNormalization

variable {p q : Code} {r b h : ℝ}

def ambientLoss (a : TrueNormalization p q r b h) (k : ℕ) : ℝ :=
  max (a.floorLoss k) (a.witness.loss k)

def ambientExponent (a : TrueNormalization p q r b h) : ℕ :=
  max a.atlas.B a.witness.exponent

theorem ambientLoss_tendsto (a : TrueNormalization p q r b h) :
    Tendsto a.ambientLoss atTop (nhds 0) := by
  change Tendsto (fun k => max (a.floorLoss k) (a.witness.loss k)) atTop (nhds 0)
  simpa only [max_self] using a.floorLoss_tendsto.max a.witness.loss_tendsto

/-- Full TRUE ChartData on the exact retained world's A/geometry, with
one original incidence piece per actual current label. -/
theorem exists_ambient_charts (a : TrueNormalization p q r b h) (k : ℕ) :
    ∃ Λ : Fin (W p (a.witness.sample k)) →
        ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k)),
      ChartData p a.ambientExponent r b (h + a.ambientLoss k) (a.ambientLoss k) true
        (a.witness.sample k) (a.witness.T k) (W q k) (a.witness.world k) (a.witness.block k)
        (a.witness.assignment k) (a.ambientSelected k) (a.witness.center k) (a.witness.speed k)
        (a.witness.width k) (a.witness.polynomial k) Λ := by
  rcases a with ⟨hp, atlas, M', D', d', out, heq⟩
  cases heq
  have hc := out.true_ambient_charts hp atlas.true_data k
  change ∃ Λ, ChartData p (max atlas.B out.witness.exponent) r b
    (h + max (atlas.ε (out.sample k)) (out.witness.loss k))
    (max (atlas.ε (out.sample k)) (out.witness.loss k)) true
    (out.witness.sample k) (out.witness.T k) (W out.code k)
    (out.witness.world k) (out.witness.block k) (out.witness.assignment k)
    (fun i => atlas.C (out.sample k) (out.embedding k i))
    (out.witness.center k) (out.witness.speed k) (out.witness.width k)
    (out.witness.polynomial k) Λ
  rw [out.data_eq]
  exact ⟨_, hc⟩

/-- Choose the full-piece lists once, retaining the current world labels. -/
def ambientLists (a : TrueNormalization p q r b h) (k : ℕ) :
    Fin (W p (a.witness.sample k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k)) :=
  Classical.choose (a.exists_ambient_charts k)

theorem ambient_charts (a : TrueNormalization p q r b h) (k : ℕ) :
    ChartData p a.ambientExponent r b (h + a.ambientLoss k) (a.ambientLoss k) true
      (a.witness.sample k) (a.witness.T k) (W q k) (a.witness.world k) (a.witness.block k)
      (a.witness.assignment k) (a.ambientSelected k) (a.witness.center k) (a.witness.speed k)
      (a.witness.width k) (a.witness.polynomial k) (a.ambientLists k) :=
  Classical.choose_spec (a.exists_ambient_charts k)

end TrueNormalization

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
