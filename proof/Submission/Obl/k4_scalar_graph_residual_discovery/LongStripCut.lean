/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file LongStripCut.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.StripBudget

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_initial_horizon_bound

noncomputable section

/-- One measurable cut makes every selected strip entry long in the
EARLIER label set. Its loss is charged globally to the unchanged prior.
Later current-mass floors may prune further without asserting that the
earlier duration is preserved under those restrictions. -/
theorem exists_simultaneous_long_strip_cut {σ : Type*} [Fintype σ]
    (ν : Measure ScalarLine) [SFinite ν] (μ : Measure ScalarIncidence)
    {c : ℝ≥0∞} (hdom : μ ≤ c • ν.prod volume)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ) {H b ρ A D : ℝ}
    (hH : 1 ≤ H) (hb : 0 < b) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hbρ : b ≤ ρ)
    (p η : σ → ℝ) (hp : ∀ s, 0 < p s) (hη : ∀ s, 0 ≤ η s)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ z ∈ E,
      |(normalPolynomial
        (row (cell ρ (leftCorner b (cell b (scalarPosition z))))) z.1).derivative.eval z.2| ≤ D)
    (hvariation : ∀ s, D * (ρ + 2 * b) + 2 * A * b ≤ p s) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ c * (∑ s, ENNReal.ofReal (6860 * H * η s)) * ν univ ∧
      ∀ z ∈ R, ∀ s,
        ENNReal.ofReal (η s * ρ) ≤
          incidenceDuration (E ∩ stripRecord b ρ (p s) row ⁻¹' {stripRecord b ρ (p s) row z}) z.1 := by
  classical
  let record (s : σ) := stripRecord b ρ (p s) row
  let entry (s : σ) (q : (Fin 3 → ℤ) × ℤ) := E ∩ record s ⁻¹' {q}
  have hentry (s : σ) (q : (Fin 3 → ℤ) × ℤ) : MeasurableSet (entry s q) :=
    hE.inter (measurable_stripRecord b ρ (p s) row (measurableSet_singleton q))
  let bad (s : σ) : Set ScalarIncidence :=
    ⋃ q : (Fin 3 → ℤ) × ℤ,
      entry s q ∩ ({l | incidenceDuration (entry s q) l < ENNReal.ofReal (η s * ρ)} ×ˢ univ)
  have hbad (s : σ) : MeasurableSet (bad s) := by
    apply MeasurableSet.iUnion
    intro q
    exact (hentry s q).inter
      ((measurableSet_lt (measurable_incidenceDuration (hentry s q)) measurable_const).prod
        MeasurableSet.univ)
  have hbadeq (s : σ) : bad s = {z | z ∈ E ∧
      incidenceDuration (E ∩ record s ⁻¹' {record s z}) z.1 < ENNReal.ofReal (η s * ρ)} := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hzq⟩ := mem_iUnion.mp hz
      have hq : record s z = q := hzq.1.2
      refine ⟨hzq.1.1, ?_⟩
      simpa only [entry, hq, mem_ofPred_eq] using hzq.2.1
    · rintro ⟨hz, hd⟩
      exact mem_iUnion.mpr ⟨record s z, ⟨⟨hz, rfl⟩, hd, mem_univ _⟩⟩
  have hcost (s : σ) : μ (bad s) ≤ c * ENNReal.ofReal (6860 * H * η s) * ν univ := by
    rw [hbadeq]
    exact short_strip_entry_mass_le_simple ν μ hdom hE row (hη s) hH hb hρ hρ₁ hbρ (hp s)
      hcoeff htime hA hD hderiv (hvariation s)
  let R := E \ ⋃ s, bad s
  refine ⟨R, hE.diff (MeasurableSet.iUnion hbad), sdiff_subset, ?_, ?_⟩
  · calc
      μ (E \ R) ≤ μ (⋃ s, bad s) := by
        apply measure_mono
        intro z hz
        exact not_not.mp (fun h => hz.2 ⟨hz.1, h⟩)
      _ ≤ ∑' s, μ (bad s) := measure_iUnion_le _
      _ = ∑ s, μ (bad s) := tsum_fintype _
      _ ≤ ∑ s, c * ENNReal.ofReal (6860 * H * η s) * ν univ :=
        Finset.sum_le_sum (fun s _ => hcost s)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  · intro z hz s
    apply le_of_not_gt
    intro hd
    have hzbad : z ∈ bad s := by
      rw [hbadeq]
      exact ⟨hz.1, hd⟩
    exact hz.2 (mem_iUnion.mpr ⟨s, hzbad⟩)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
