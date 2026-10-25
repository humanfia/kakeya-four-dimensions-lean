/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/DensityMasks.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SelectedPaths

/-! Concrete finite pure/angular density masks in all original path frames.
The exception definitions adapt the same-tree o134 work of x0438:
Submission/Obl/k4_scalar_guarded_tangent_obstruction/ExactLaw.lean and
DensityTails.lean, source branch x0438 at 2e990309978b4e84f58b1a4128b240d6351df6e4.
Here the pure depth is arbitrary and each fixed stage may test a finite grid.
Accepted finite-component and power-small operations are imported, not copied. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

def taggedEvent {n : ℕ} (A : Fin n → Set State) : Set (Fin n × State) :=
  {z | z.2 ∈ A z.1}

theorem measurableSet_taggedEvent {n : ℕ} (A : Fin n → Set State)
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (taggedEvent A) := by
  have heq : taggedEvent A = ⋃ i, ({i} ×ˢ A i) := by ext z; simp [taggedEvent]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod (hA i)

theorem worldMixture_taggedEvent (p : Code) (k : ℕ) (A : Fin (W p k) → Set State)
    (hA : ∀ i, MeasurableSet (A i)) :
    worldMixture p k (taggedEvent A) = ∑ i, ENNReal.ofReal (ω p k i) * mu p k i (A i) := by
  rw [Submission.Obl.k4_original_prior_line_extraction.measure_eq_sum_components _
    (measurableSet_taggedEvent A hA)]
  apply Finset.sum_congr rfl
  intro i _
  change worldFiber (worldMixture p k) i (A i) = _
  rw [worldFiber_worldMixture, Measure.smul_apply]
  rfl

def pureException (p : Code) (k : ℕ) (i : Fin (W p k)) (r τ : ℝ) : Set State :=
  {z | g p k i r (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL
      (N p k ^ (-r)) z) < ENNReal.ofReal (N p k ^ (-f p r - τ)) ∨
    ENNReal.ofReal (N p k ^ (-f p r + τ)) <
      g p k i r (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL
        (N p k ^ (-r)) z)}

def angularException (p : Code) (k : ℕ) (i : Fin (W p k)) (a τ : ℝ) : Set State :=
  {z | ENNReal.ofReal (N p k ^ (-f p (L p) - S p * a + τ)) <
    G p k i a (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG
      (N p k ^ (-L p)) (N p k ^ (-a)) z)}

theorem measurableSet_pureException {p : Code} (hp : Exact p) (k : ℕ)
    (i : Fin (W p k)) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L p) (τ : ℝ) :
    MeasurableSet (pureException p k i r τ) := by
  have hm := (hp.2.2.1 k i r hr hrL).1.comp
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL (N p k ^ (-r)))
  exact (measurableSet_lt hm measurable_const).union (measurableSet_lt measurable_const hm)

theorem measurableSet_angularException {p : Code} (hp : Exact p) (k : ℕ)
    (i : Fin (W p k)) {a : ℝ} (ha : 0 < a) (haU : a ≤ U p) (τ : ℝ) :
    MeasurableSet (angularException p k i a τ) := by
  exact measurableSet_lt measurable_const ((hp.2.2.2.1 k i a ha haU).1.comp
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _))

theorem pureException_powerSmall {p : Code} (hp : Exact p) {r τ : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ L p) (hτ : 0 < τ) :
    IsPowerSmall (N p) (fun k => worldMixture p k
      (taggedEvent (fun i => pureException p k i r τ))) := by
  obtain ⟨c, hc, hbound⟩ := hp.2.2.2.2.2.1 r τ hr hrL hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with k hk
  rw [worldMixture_taggedEvent _ _ _ (fun i => measurableSet_pureException hp k i hr hrL τ)]
  exact hk

theorem angularException_powerSmall {p : Code} (hp : Exact p) {a τ : ℝ}
    (ha : 0 < a) (haU : a ≤ U p) (hτ : 0 < τ) :
    IsPowerSmall (N p) (fun k => worldMixture p k
      (taggedEvent (fun i => angularException p k i a τ))) := by
  obtain ⟨c, hc, hbound⟩ := hp.2.2.2.2.2.2.2 a τ ha haU hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with k hk
  rw [worldMixture_taggedEvent _ _ _ (fun i => measurableSet_angularException hp k i ha haU τ)]
  exact hk

theorem powerSmall_finite_union {ι : Type*} {X : ℕ → Type*}
    [∀ k, MeasurableSpace (X k)] (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (X k)) (A : ι → (k : ℕ) → Set (X k))
    (hA : ∀ i, IsPowerSmall N (fun k => μ k (A i k))) (F : Finset ι) :
    IsPowerSmall N (fun k => μ k (⋃ i ∈ F, A i k)) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, Eventually.of_forall fun k => by simp⟩
  | @insert i F hi ih =>
    apply ((hA i).add hN ih).mono
    exact Eventually.of_forall fun k => by
      have heq : (⋃ j ∈ insert i F, A j k) = A i k ∪ ⋃ j ∈ F, A j k := by
        ext z
        simp
      rw [heq]
      exact measure_union_le _ _

/-- A fixed finite family of original scales at every potential parent.
The family and tolerances are chosen before the inner sample. -/
structure DensityGrid where
  count : Code → ℕ
  pureDepth : (p : Code) → Fin (count p) → ℝ
  angularDepth : (p : Code) → Fin (count p) → ℝ
  tolerance : (p : Code) → Fin (count p) → ℝ
  valid : ∀ p, Exact p → ∀ i,
    0 ≤ pureDepth p i ∧ pureDepth p i ≤ L p ∧
    0 < angularDepth p i ∧ angularDepth p i ≤ U p ∧ 0 < tolerance p i

namespace DensityGrid

def exceptions (grid : DensityGrid) (p : Code) (k : ℕ) : Set (Fin (W p k) × State) := by
  classical
  exact if Exact p then ⋃ i : Fin (grid.count p),
    taggedEvent (fun a => pureException p k a (grid.pureDepth p i) (grid.tolerance p i)) ∪
    taggedEvent (fun a => angularException p k a (grid.angularDepth p i) (grid.tolerance p i))
  else ∅

theorem measurableSet_exceptions (grid : DensityGrid) (p : Code) (k : ℕ) :
    MeasurableSet (grid.exceptions p k) := by
  classical
  unfold exceptions
  split_ifs with hp
  · apply MeasurableSet.iUnion
    intro i
    obtain ⟨hr, hrL, ha, haU, hτ⟩ := grid.valid p hp i
    exact (measurableSet_taggedEvent _ (fun a => measurableSet_pureException hp k a hr hrL _)).union
      (measurableSet_taggedEvent _ (fun a => measurableSet_angularException hp k a ha haU _))
  · exact MeasurableSet.empty

theorem exceptions_powerSmall (grid : DensityGrid) (p : Code) :
    IsPowerSmall (N p) (fun k => worldMixture p k (grid.exceptions p k)) := by
  classical
  by_cases hp : Exact p
  · have hsingle (i : Fin (grid.count p)) : IsPowerSmall (N p) (fun k => worldMixture p k
        (taggedEvent (fun a => pureException p k a (grid.pureDepth p i) (grid.tolerance p i)) ∪
          taggedEvent (fun a => angularException p k a (grid.angularDepth p i) (grid.tolerance p i)))) := by
      obtain ⟨hr, hrL, ha, haU, hτ⟩ := grid.valid p hp i
      apply ((pureException_powerSmall hp hr hrL hτ).add hp.1.2.1
        (angularException_powerSmall hp ha haU hτ)).mono
      exact Eventually.of_forall fun k => measure_union_le _ _
    simpa only [exceptions, ite_eq_left hp, Finset.mem_univ, iUnion_true] using
      powerSmall_finite_union (N p) hp.1.2.1 (worldMixture p) _ hsingle Finset.univ
  · refine ⟨1, by norm_num, Eventually.of_forall fun k => ?_⟩
    simp only [exceptions, ite_eq_right hp, measure_empty]
    exact bot_le

end DensityGrid

namespace RefinementChain

theorem allSuffixes_densityExceptions_powerSmall {p z : Code} (chain : RefinementChain p z)
    (grid : DensityGrid) : chain.AllSuffixes (fun q _ =>
      IsPowerSmall (N q) (fun k => worldMixture q k (grid.exceptions q k))) := by
  induction chain with
  | nil p => exact grid.exceptions_powerSmall p
  | cons w hp tail ih => exact ⟨grid.exceptions_powerSmall _, ih⟩

theorem eventually_densityCore_mass_half {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (grid : DensityGrid) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture z k (chain.commonCore grid.exceptions k) :=
  chain.eventually_commonCore_mass_half hz grid.exceptions grid.measurableSet_exceptions
    (chain.allSuffixes_densityExceptions_powerSmall grid)

theorem densityCore_originalMass_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N z k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) *
        chain.selectedWorldLaw k (chain.commonCore grid.exceptions k) g univ :=
  chain.selectedWorldLaw_mass_subpower hz (chain.commonCore grid.exceptions)
    (chain.eventually_densityCore_mass_half hz grid) ε hε

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
