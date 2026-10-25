/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/SuffixReferences.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathReference

/-! One subpower reference factor controls the common path law in every
intermediate original frame. The factor uses the complete path mass, so
potential parent choices do not require independent normalizations. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def AllSuffixes {p z : Code} (chain : RefinementChain p z)
    (P : (q : Code) → RefinementChain q z → Prop) : Prop :=
  match chain with
  | .nil p => P p (.nil p)
  | .cons w hp tail => P _ (.cons w hp tail) ∧ tail.AllSuffixes P

theorem allSuffixes_mono {p z : Code} (chain : RefinementChain p z)
    {P Q : (q : Code) → RefinementChain q z → Prop}
    (hPQ : ∀ q suffix, P q suffix → Q q suffix) (hP : chain.AllSuffixes P) :
    chain.AllSuffixes Q := by
  induction chain with
  | nil p => exact hPQ p (.nil p) hP
  | cons w hp tail ih => exact ⟨hPQ _ _ hP.1, ih hPQ hP.2⟩

theorem referenceFactor_tail_le {p q z : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (tail : RefinementChain q z)
    (hz : Exact z) (k : ℕ) :
    tail.referenceFactor k ≤ (RefinementChain.cons w hp tail).referenceFactor k := by
  have hbudget : (RefinementChain.cons w hp tail).budget k ≤ tail.budget k := by
    change normalizer w (tail.sample k) * tail.budget k ≤ tail.budget k
    calc
      _ ≤ 1 * tail.budget k :=
        mul_le_mul_of_nonneg_right (normalizer_le_one w hp _) (tail.budget_pos k).le
      _ = _ := one_mul _
  have hmass : (RefinementChain.cons w hp tail).originalLaw k univ ≤ tail.originalLaw k univ := by
    rw [(RefinementChain.cons w hp tail).originalLaw_univ, tail.originalLaw_univ]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl
  apply inv_anti₀ ((RefinementChain.cons w hp tail).originalLaw_mass_toReal_pos hz k)
  exact ENNReal.toReal_mono ((tail.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne hmass

/-- The complete original path's reciprocal mass bounds that of every
suffix, termwise, before taking any exact-sequence or outer limit. -/
theorem allSuffixes_referenceFactor_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    chain.AllSuffixes (fun _ suffix => suffix.referenceFactor k ≤ chain.referenceFactor k) := by
  induction chain with
  | nil => exact le_rfl
  | cons w hp tail ih =>
    refine ⟨le_rfl, tail.allSuffixes_mono (fun q suffix hs => ?_) (ih hz)⟩
    exact hs.trans (referenceFactor_tail_le w hp tail hz k)

/-- Every intermediate view of the common final probability is dominated
by its own full original mixture with ONE shared subpower factor. -/
theorem allSuffixes_probability_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    chain.AllSuffixes (fun q suffix => suffix.probability k ≤
      ENNReal.ofReal (chain.referenceFactor k) • worldMixture q (suffix.sample k)) := by
  apply chain.allSuffixes_mono (P := fun _ suffix =>
    suffix.referenceFactor k ≤ chain.referenceFactor k)
    (fun q suffix hs => ?_) (chain.allSuffixes_referenceFactor_le hz k)
  apply (suffix.probability_le_originalReference hz k).trans
  apply Measure.le_iff.mpr
  intro S _
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hs) le_rfl

theorem allSuffixes_commonLaw_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    chain.AllSuffixes (fun q suffix => (normalizedWorldMixture z k).map (suffix.pullback k) ≤
      ENNReal.ofReal (chain.referenceFactor k) • worldMixture q (suffix.sample k)) := by
  apply chain.allSuffixes_mono (fun q suffix hs => ?_) (chain.allSuffixes_probability_le hz k)
  rw [← suffix.probability_eq_map_finalMixture k]
  exact hs

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
