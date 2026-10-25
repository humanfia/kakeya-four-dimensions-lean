/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/MeasuredPaths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CriticalPaths

/-! A finite chain of actual scalar refinements has a common original-world
path measure. Every layer keeps its original full assigned priors, while an
arbitrary sparse final incidence selection pulls back to an original-law
submeasure with the product of actual normalization budgets. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

inductive RefinementChain : Code → Code → Type where
  | nil (p : Code) : RefinementChain p p
  | cons {p q z : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)
      (hp : Exact p) (tail : RefinementChain q z) : RefinementChain p z

namespace RefinementChain

def sample {p z : Code} (chain : RefinementChain p z) : ℕ → ℕ :=
  match chain with
  | .nil _ => id
  | .cons w _ tail => w.sample ∘ tail.sample

def budget {p z : Code} (chain : RefinementChain p z) (k : ℕ) : ℝ :=
  match chain with
  | .nil _ => 1
  | .cons w _ tail => normalizer w (tail.sample k) * tail.budget k

def pullback {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Fin (W z k) × State → Fin (W p (chain.sample k)) × State :=
  match chain with
  | .nil _ => id
  | .cons w hp tail => pullbackMap w hp (tail.sample k) ∘ tail.pullback k

theorem sample_strictMono {p z : Code} (chain : RefinementChain p z) :
    StrictMono chain.sample := by
  induction chain with
  | nil => exact strictMono_id
  | cons w hp tail ih => exact w.sample_strictMono.comp ih

theorem resolution {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    N z k = N p (chain.sample k) := by
  induction chain with
  | nil => rfl
  | cons w hp tail ih => exact ih.trans (w.charts (tail.sample k)).1

theorem budget_pos {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    0 < chain.budget k := by
  induction chain with
  | nil => exact zero_lt_one
  | cons w hp tail ih => exact mul_pos (normalizer_pos w (tail.sample k)) ih

theorem measurable_pullback {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Measurable (chain.pullback k) := by
  induction chain with
  | nil => exact measurable_id
  | cons w hp tail ih => exact (measurable_pullbackMap w hp (tail.sample k)).comp ih

/-- The entire finite chain retains arbitrary later sparse selections as
submeasures of its original world law. -/
theorem submeasure_pullback_le {p z : Code} (chain : RefinementChain p z) :
    ∀ (k : ℕ) (ρ : Measure (Fin (W z k) × State)), ρ ≤ worldMixture z k →
      ENNReal.ofReal (chain.budget k) • ρ.map (chain.pullback k) ≤
        worldMixture p (chain.sample k) := by
  induction chain with
  | nil p =>
    intro k ρ hρ
    change ENNReal.ofReal (1 : ℝ) • Measure.map (id : (Fin (W p k) × State) → _) ρ ≤
      worldMixture p k
    rw [ENNReal.ofReal_one, one_smul, Measure.map_id]
    exact hρ
  | cons w hp tail ih =>
    intro k ρ hρ
    have htail := ih k ρ hρ
    have hparent := PathMeasures.submeasure_pullback_le w hp (tail.sample k) _ htail
    rw [Measure.map_smul _ (measurable_pullbackMap w hp (tail.sample k)).aemeasurable,
      Measure.map_map (measurable_pullbackMap w hp (tail.sample k))
        (tail.measurable_pullback k), smul_smul,
      ← ENNReal.ofReal_mul (normalizer_pos w (tail.sample k)).le] at hparent
    exact hparent

def originalLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Measure (Fin (W p (chain.sample k)) × State) :=
  ENNReal.ofReal (chain.budget k) • (worldMixture z k).map (chain.pullback k)

theorem originalLaw_le {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    chain.originalLaw k ≤ worldMixture p (chain.sample k) :=
  chain.submeasure_pullback_le k _ le_rfl

theorem originalLaw_univ {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    chain.originalLaw k univ = ENNReal.ofReal (chain.budget k) * worldMixture z k univ := by
  rw [originalLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) MeasurableSet.univ, preimage_univ]
  rfl

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

/-- The actual layer refinements of a finite critical path realize a common
original-world incidence law, with all full-prior witnesses retained. -/
theorem nonempty_refinementChain {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets)
    (i : ℕ) (hi : path.AllLayers i) :
    Nonempty (RefinementChain (source.problem i) (path.finalFamily.problem i)) := by
  induction path with
  | nil source start => exact ⟨.nil (source.problem i)⟩
  | @cons source start r rs hstart hr node tail ih =>
    obtain ⟨chain⟩ := ih hi.2
    obtain ⟨w⟩ := refinement_iff_nonempty_witness.mp hi.1.refinement
    exact ⟨.cons w (source.angular i).1 chain⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath
