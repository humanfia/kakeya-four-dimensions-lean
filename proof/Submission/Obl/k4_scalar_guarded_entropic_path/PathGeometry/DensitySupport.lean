/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/DensitySupport.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks

/-! Every intermediate original-world view of the common density core
avoids its own original exceptional sets. The conclusion survives all later
dominated restrictions and includes zero-weight original worlds. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem originalFibers_null_of_tagged_subset {p : Code} {k : ℕ}
    (ρ : Measure (Fin (W p k) × State)) (A : Fin (W p k) → Set State)
    (hA : ∀ i, MeasurableSet (A i)) {B : Set (Fin (W p k) × State)}
    (hB : ρ B = 0) (hsub : taggedEvent A ⊆ B) (i : Fin (W p k)) :
    originalFibers p k ρ i (A i) = 0 := by
  have hf : worldFiber ρ i (A i) = 0 := by
    rw [worldFiber_apply _ _ (hA i)]
    apply measure_mono_null (t := B) ?_ hB
    rintro z ⟨hz, ha⟩
    apply hsub
    change z.2 ∈ A z.1
    simpa only [mem_singleton_iff.mp hz] using ha
  rw [originalFibers, Measure.smul_apply, hf, smul_zero]

namespace RefinementChain

theorem allSuffixes_avoid_badSet {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State)) (k : ℕ)
    (G : Set (Fin (W z k) × State)) (hG : G ⊆ (chain.badSet bad k)ᶜ) :
    chain.AllSuffixes (fun q suffix => G ⊆
      (suffix.pullback k ⁻¹' bad q (suffix.sample k))ᶜ) := by
  induction chain with
  | nil p =>
    intro a ha hb
    exact hG ha (Or.inl hb)
  | cons w hp tail ih =>
    refine ⟨?_, ih G ?_⟩
    · intro a ha hb
      exact hG ha (Or.inl hb)
    · intro a ha hb
      exact hG ha (Or.inr hb)

theorem selectedLaw_null_of_avoid {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (G : Set (Fin (W z k) × State)) {B : Set (Fin (W p (chain.sample k)) × State)}
    (hB : MeasurableSet B) (hG : G ⊆ (chain.pullback k ⁻¹' B)ᶜ) :
    chain.selectedLaw k G B = 0 := by
  have hempty : chain.pullback k ⁻¹' B ∩ G = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro a ⟨ha, hGa⟩
    exact hG hGa ha
  rw [selectedLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) hB,
    Measure.restrict_apply (hB.preimage (chain.measurable_pullback k)), hempty,
    measure_empty, smul_zero]

/-- Every original potential parent sees no density exceptions under its
view of the SAME common core, with its own unchanged original weights. -/
theorem allSuffixes_densityCore_exception_null {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (grid : DensityGrid) (k : ℕ) :
    chain.AllSuffixes (fun q suffix => ∀ (j : Fin (grid.count q))
      (i : Fin (W q (suffix.sample k))),
      suffix.selectedWorldLaw k (chain.commonCore grid.exceptions k) i
        (pureException q (suffix.sample k) i (grid.pureDepth q j) (grid.tolerance q j)) = 0 ∧
      suffix.selectedWorldLaw k (chain.commonCore grid.exceptions k) i
        (angularException q (suffix.sample k) i (grid.angularDepth q j) (grid.tolerance q j)) = 0) := by
  have havoid := chain.allSuffixes_avoid_badSet grid.exceptions k
    (chain.commonCore grid.exceptions k) inter_subset_right
  apply chain.allSuffixes_mono (fun q suffix hs => ?_) havoid
  have hq : Exact q := suffix.source_exact hz
  have hnull := suffix.selectedLaw_null_of_avoid k (chain.commonCore grid.exceptions k)
    (grid.measurableSet_exceptions q _) hs
  intro j i
  obtain ⟨hr, hrL, ha, haU, hτ⟩ := grid.valid q hq j
  constructor
  · apply originalFibers_null_of_tagged_subset _ _
      (fun i => measurableSet_pureException hq _ i hr hrL _) hnull ?_ i
    intro a ha
    classical
    rw [DensityGrid.exceptions, ite_eq_left hq]
    exact mem_iUnion.mpr ⟨j, Or.inl ha⟩
  · apply originalFibers_null_of_tagged_subset _ _
      (fun i => measurableSet_angularException hq _ i ha haU _) hnull ?_ i
    intro a ha
    classical
    rw [DensityGrid.exceptions, ite_eq_left hq]
    exact mem_iUnion.mpr ⟨j, Or.inr ha⟩

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
