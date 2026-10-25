-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreLists.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreStatement
import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts
import Submission.Lib.K4ContinuousPlanks.Discretization

/-!
# Coarse graph lists as finite sets

The frozen coarse row lists are cardinality bounds on the positive row bins of
each coarse cube. Since the graph rows are bounded, these sets are finite, and
every incidence whose (fine cube, coarse cube) class is positive has its row
bin in the list of its own coarse cube.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set

/-- The (fine cube, coarse cube) class of an incidence. -/
noncomputable def coreCode (N B rT : ℝ) (p : Incidence) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (physCube N B p, physCube N rT p)

-- Reuse the identical measurability theorem from DataFacts; avoid a duplicate public declaration.
theorem measurable_coreCode (N B rT : ℝ) : Measurable (coreCode N B rT) :=
  (measurable_physCube N B).prodMk (measurable_physCube N rT)

/-- The frozen coarse lists, as finite sets with the frozen cardinality bound. -/
theorem exists_coarse_lists (ρ : Measure Incidence) (E : Set Incidence) (hE : MeasurableSet E)
    (G : (Fin 3 → ℤ) → Fin 2 → ℝ) (N rT B Λ : ℝ) (hε : 0 < N ^ (-rT))
    (hG : ∀ p ∈ E, ∀ e, |G (physCube N B p) e| ≤ Λ)
    (hcount : ∀ q : Fin 3 → ℤ, ({w : Fin 2 → ℤ | ρ.restrict E
      {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0}.ncard : ℝ) ≤ Λ) :
    ∃ L : (Fin 3 → ℤ) → Finset (Fin 2 → ℤ), (∀ q, ((L q).card : ℝ) ≤ Λ) ∧
      ∀ p : Incidence, ρ.restrict E {p' | coreCode N B rT p' = coreCode N B rT p} ≠ 0 →
        rowBin N rT (G (physCube N B p)) ∈ L (physCube N rT p) := by
  classical
  set W : (Fin 3 → ℤ) → Set (Fin 2 → ℤ) := fun q => {w : Fin 2 → ℤ | ρ.restrict E
      {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0} with hW
  have hrange : (Set.range (fun p : E => (fun e => ⌊G (physCube N B p.1) e / N ^ (-rT)⌋ :
      Fin 2 → ℤ))).Finite :=
    Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
      (fun p : E => G (physCube N B p.1)) Λ (fun p e => hG p.1 p.2 e) hε
  have hfin : ∀ q, (W q).Finite := by
    intro q
    apply hrange.subset
    intro w hw
    have hne : ρ.restrict E
        {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0 := hw
    rw [Measure.restrict_apply' hE] at hne
    obtain ⟨p, hp, hpE⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨⟨p, hpE⟩, hp.2⟩
  refine ⟨fun q => (hfin q).toFinset, ?_, ?_⟩
  · intro q
    rw [← Set.ncard_eq_toFinset_card (W q) (hfin q)]
    exact hcount q
  · intro p hp
    rw [Set.Finite.mem_toFinset]
    show ρ.restrict E {p' | physCube N rT p' = physCube N rT p ∧
      rowBin N rT (G (physCube N B p')) = rowBin N rT (G (physCube N B p))} ≠ 0
    intro h0
    apply hp
    apply measure_mono_null _ h0
    intro p' hp'
    have hc : coreCode N B rT p' = coreCode N B rT p := hp'
    simp only [coreCode, Prod.mk.injEq] at hc
    exact ⟨hc.2, by rw [hc.1]⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
