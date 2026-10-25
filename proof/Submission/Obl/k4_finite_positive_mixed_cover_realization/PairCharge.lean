/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/PairCharge.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.PairLists
import Submission.Obl.k4_finite_positive_mixed_cover_realization.AngularCharge

/-!
The analytic strip discard uses candidate/deep-chart pairs as temporary
labels. The original deep list and per-ancestor candidate count bound their
list size. Original density exceptions are removed before this estimate,
so they do not pay the larger temporary label multiplicity.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set

open Classical in
/-- Good misaligned pair mass is charged directly by the ORIGINAL joint cap
and pure density. The pair labels are not labels of the final output atlas. -/
theorem known_parented_pair_velocity_charge
    {Ω X V A D P : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V] [Fintype A] [Fintype D]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (obs : Ω → X) (vel : Ω → V) (hobs : Measurable obs) (hvel : Measurable vel)
    (g : X → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ν.withDensity g)
    (G : X × V → ENNReal) (hG : Measurable G)
    (hjoint : μ.map (fun p => (obs p, vel p)) = (ν.prod Measure.count).withDensity G)
    (F : A × D → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (cells : A × D → Finset V)
    (hvelocity : ∀ i p, p ∈ F i → vel p ∈ cells i)
    (parent : A → P) (ancestor : D → P) (deepLists : X → Finset D)
    (hknown : ∀ i p, p ∈ F i → i.2 ∈ deepLists (obs p) ∧ parent i.1 = ancestor i.2)
    {a b v K R : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hv : 0 ≤ v) (hR : 0 ≤ R)
    (hcard : ∀ i, ((cells i).card : ℝ) ≤ v)
    (hlists : ∀ x, ((deepLists x).card : ℝ) ≤ K)
    (hfiber : ∀ d,
      ((Finset.univ.filter (fun c => parent c = ancestor d)).card : ℝ) ≤ R) :
    (∑ i, μ {p | p ∈ F i ∧ G (obs p, vel p) ≤ ENNReal.ofReal a ∧
      ENNReal.ofReal b ≤ g (obs p)}) ≤
        ENNReal.ofReal (a * v / b) * ENNReal.ofReal (K * R) * μ univ := by
  classical
  apply known_label_velocity_charge μ ν obs vel hobs hvel g hg hlaw G hG hjoint
    F hF cells hvelocity
    (fun x => analyticalPairList parent ancestor (deepLists x))
    (fun i p hp => (mem_analyticalPairList parent ancestor (deepLists (obs p)) i.1 i.2).mpr
      (hknown i p hp)) ha hb hv hcard (ENNReal.ofReal (K * R))
  intro x
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (card_analyticalPairList_le parent ancestor (deepLists x) (hlists x) hR (fun d _ => hfiber d))

end Submission.Obl.k4_finite_positive_mixed_cover_realization
