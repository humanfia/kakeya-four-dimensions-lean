/- Adapted from: here:o107 (session x0359, branch x0359-libcharge, commit dbbe0acd). -/
import Mathlib
import Submission.Lib.K4AngularCharge.AngularCharge
import Submission.Lib.K4XInterface

/-!
# The angular charge for one world of the frozen interface X

`x_known_label_charge` specializes `known_label_charge` to the frozen data: the incidence law
`(ν × dt)|E` of a world, its terminal observation `gobs B a`, the velocity cells
`⌊v_j / u⌋`, the pure density `g` and the angular density `G` of the problem predicate.
`measurable_gobs`, `measurable_gcell`, `finite_restrict_prod` supply the side conditions.
-/

namespace Submission.Lib.K4AngularCharge

open Submission.Lib.K4XInterface

open MeasureTheory

open scoped ENNReal

theorem measurable_gobs (B a : ℝ) : Measurable (gobs B a) := by
  unfold gobs gx
  refine Measurable.prodMk ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  · refine Int.measurable_floor.comp ?_
    simp
    fun_prop

theorem measurable_gcell (u : ℝ) :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => fun j : Fin 2 => ⌊(gv p.1) j / u⌋) := by
  refine measurable_pi_iff.mpr fun j => Int.measurable_floor.comp ?_
  fin_cases j <;> simp [gv] <;> fun_prop

theorem finite_restrict_prod {ν : Measure (ℕ × (Fin 6 → ℝ))} [IsProbabilityMeasure ν]
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) :
    IsFiniteMeasure ((ν.prod volume).restrict E) := by
  constructor
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  calc (ν.prod volume) E ≤ (ν.prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by rw [Measure.prod_prod]; simp
    _ < ⊤ := ENNReal.one_lt_top

/-- `known_label_charge` for one world of the frozen interface X: labels known through the
terminal observation `gobs B a` (lists of size `κ`) whose velocity cells at width `u` lie in at
most `M` cells carry, where the angular density `G` is at most `α` and the pure density `g` at
least `β`, at most `κ M (α / β)` times the world's incidence mass. -/
theorem x_known_label_charge {ν : Measure (ℕ × (Fin 6 → ℝ))} [IsProbabilityMeasure ν]
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (B a u : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : Measurable g)
    (hmap : Measure.map (gobs B a) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity g)
    (G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞) (hG : Measurable G)
    (hmapG : Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        (gobs B a p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋)) ((ν.prod volume).restrict E) =
      ((volume.prod Measure.count).prod Measure.count).withDensity G)
    {ι : Type*} [Fintype ι] (F : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hF : ∀ b, MeasurableSet (F b)) (lst : EuclideanSpace ℝ (Fin 3) × ℤ → Finset ι)
    (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (gobs B a p)) (κ : ℕ) (hκ : ∀ o, (lst o).card ≤ κ)
    (V : ι → Finset (Fin 2 → ℤ))
    (hV : ∀ b, ∀ p ∈ F b, (fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∈ V b) (M : ℕ)
    (hM : ∀ b, (V b).card ≤ M) (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    ∑ b, ((ν.prod volume).restrict E) (F b ∩ {p | G (gobs B a p, fun j : Fin 2 =>
        ⌊(gv p.1) j / u⌋) ≤ α ∧ β ≤ g (gobs B a p)}) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) * ((ν.prod volume).restrict E) Set.univ := by
  have := finite_restrict_prod (ν := ν) hE
  exact known_label_charge ((ν.prod volume).restrict E) (gobs B a) (measurable_gobs B a)
    (fun p => fun j : Fin 2 => ⌊(gv p.1) j / u⌋) (measurable_gcell u)
    (volume.prod Measure.count) g hg hmap G hG hmapG F hF lst hlst κ hκ V hV M hM α β hβ

end Submission.Lib.K4AngularCharge
