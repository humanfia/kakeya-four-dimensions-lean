-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/JensenCoverage.lean.
import Submission.Obl.k4_scalar_angular_pair_agreement.AllPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

/-! Jensen coverage with source entries and the original priors. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Raw pairs before analytic masks: a selected source, and a selected witness
time in the same coarse block. -/
def rawSourcePairs {X : Type*} (S : Set (X × ℝ)) (I : Set ℝ)
    (W : Set (X × ℝ)) : Set (X × (ℝ × ℝ)) :=
  {p | (p.1, p.2.1) ∈ S ∧ p.2.2 ∈ I ∧ (p.1, p.2.2) ∈ W}

theorem measurableSet_rawSourcePairs {X : Type*} [MeasurableSpace X]
    {S W : Set (X × ℝ)} {I : Set ℝ} (hS : MeasurableSet S)
    (hI : MeasurableSet I) (hW : MeasurableSet W) :
    MeasurableSet (rawSourcePairs S I W) :=
  (hS.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
    ((hI.preimage measurable_snd.snd).inter
      (hW.preimage (measurable_fst.prodMk measurable_snd.snd)))

/-- The sum of raw source-indexed pair masses is at least the square of the
selected one-time mass. The block normalization and all original world weights
are retained. -/
theorem source_indexed_pair_lower {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W T : ℕ) (ν : Fin W → Measure X) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin W → ℝ≥0∞) (hω : ∑ w, ω w = 1)
    (γ : ι → Fin W) (j : ι → Fin (2 ^ T))
    (S : ι → Set (X × ℝ)) (hS : ∀ s, MeasurableSet (S s))
    (hdisj : ∀ s s', s ≠ s' → γ s = γ s' → j s = j s' → Disjoint (S s) (S s'))
    (hblock : ∀ s p, p ∈ S s → p.2 ∈ I T (j s))
    (Sel : Fin W → Set (X × ℝ)) (hSel : ∀ w, MeasurableSet (Sel w))
    (hSSel : ∀ s, S s ⊆ Sel (γ s))
    {m₀ : ℝ≥0∞} (hm₀ : m₀ ≠ ⊤)
    (hmass : m₀ ≤ ∑ s, ω (γ s) * ((ν (γ s)).prod volume) (S s)) :
    m₀ ^ 2 ≤ ∑ s, ω (γ s) * (2 ^ T : ℕ) *
      ((ν (γ s)).prod (volume.prod volume))
        (rawSourcePairs (S s) (I T (j s)) (Sel (γ s))) := by
  classical
  let D (w : Fin W) (b : Fin (2 ^ T)) : Set (X × ℝ) :=
    {p | ∃ s, (γ s, j s) = (w, b) ∧ p ∈ S s}
  have hD (w : Fin W) (b : Fin (2 ^ T)) : MeasurableSet (D w b) := by
    simp only [D, ofPred_exists]
    apply MeasurableSet.iUnion
    intro s
    by_cases h : (γ s, j s) = (w, b)
    · simpa only [h, true_and, ofPred_mem_eq] using hS s
    · simp only [h, false_and, ofPred_false, MeasurableSet.empty]
  have hsplit : (∑ w, ∑ b, ω w * ((ν w).prod volume) (D w b)) =
      ∑ s, ω (γ s) * ((ν (γ s)).prod volume) (S s) := by
    have h := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
      (fun a : Fin W × Fin (2 ^ T) => (ν a.1).prod volume)
      (fun a => ω a.1) (fun _ : ι => True) (fun s => (γ s, j s)) S
      (fun s _ => hS s) (fun s s' _ _ hne heq => hdisj s s' hne
        (congrArg Prod.fst heq) (congrArg Prod.snd heq))
    simpa only [Fintype.sum_prod_type, true_and, ite_true, D] using h
  have hpair := Submission.Obl.k4_scalar_angular_pair_agreement.all_pairs_lower
    (Nat.two_pow_pos T) ω hω ν D hD hm₀ (by simpa only [hsplit] using hmass)
  let H (s : ι) := rawSourcePairs (S s) (I T (j s)) (Sel (γ s))
  have hH (s : ι) : MeasurableSet (H s) :=
    measurableSet_rawSourcePairs (hS s)
      (Submission.Obl.k4_scalar_angular_pair_agreement.measurableSet_I _ _) (hSel (γ s))
  let U (w : Fin W) (b : Fin (2 ^ T)) : Set (X × (ℝ × ℝ)) :=
    {p | ∃ s, (γ s, j s) = (w, b) ∧ p ∈ H s}
  have hsplitH : (∑ w, ∑ b, ω w * (2 ^ T : ℕ) *
      ((ν w).prod (volume.prod volume)) (U w b)) =
      ∑ s, ω (γ s) * (2 ^ T : ℕ) * ((ν (γ s)).prod (volume.prod volume)) (H s) := by
    have h := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
      (fun a : Fin W × Fin (2 ^ T) => (ν a.1).prod (volume.prod volume))
      (fun a => ω a.1 * (2 ^ T : ℕ)) (fun _ : ι => True) (fun s => (γ s, j s)) H
      (fun s _ => hH s) (by
        intro s s' _ _ hne heq
        apply disjoint_left.mpr
        intro p hp hp'
        exact disjoint_left.mp (hdisj s s' hne (congrArg Prod.fst heq)
          (congrArg Prod.snd heq)) hp.1 hp'.1)
    simpa only [Fintype.sum_prod_type, true_and, ite_true, U] using h
  apply hpair.trans
  rw [← hsplitH]
  apply Finset.sum_le_sum
  intro w _
  apply Finset.sum_le_sum
  intro b _
  gcongr
  rintro p ⟨⟨s, hs, hp⟩, ⟨s', hs', hp'⟩⟩
  refine ⟨s, hs, hp, ?_, ?_⟩
  · have hj : j s = b := congrArg Prod.snd hs
    have hj' : j s' = b := congrArg Prod.snd hs'
    simpa only [hj, hj'] using hblock s' (p.1, p.2.2) hp'
  · have hγ : γ s = w := congrArg Prod.fst hs
    have hγ' : γ s' = w := congrArg Prod.fst hs'
    simpa only [hγ, hγ'] using hSSel s' hp'

end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
