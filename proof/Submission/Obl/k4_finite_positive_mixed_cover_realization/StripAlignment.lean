/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripAlignment.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry

/-!
Alignment of candidate strips with deeper true strips. Separated strip
parameters confine the common velocity to a small ball. Charging that ball
under the unchanged deeper reference law and summing the per-parent candidate
budgets removes the misaligned incidences.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace ENNReal

/-- Separated fitted strips confine every common velocity to one small ball.
The center is constant for the whole pair of strips. -/
theorem unit_strip_overlap_ball {Ω : Type*} (vel : Ω → Plane) (S : Set Ω)
    {n m : Plane} {β γ r gap V : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hV : 0 ≤ V)
    (hgap : 0 < gap) (hsmall : 4 * r ≤ gap)
    (hsep : gap ≤ ‖n - m‖ + |β - γ|)
    (hsep' : gap ≤ ‖n + m‖ + |β + γ|)
    (hS : ∀ p ∈ S, ‖vel p‖ ≤ V ∧
      |inner ℝ (vel p) n - β| ≤ r ∧ |inner ℝ (vel p) m - γ| ≤ r) :
    ∃ center : Plane, ∀ p ∈ S, dist (vel p) center ≤ 32 * (1 + V) * r / gap := by
  by_cases hnonempty : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hnonempty
    obtain ⟨hv₀, hn₀, hm₀⟩ := hS p₀ hp₀
    have hwedge := separated_strip_wedge hn hm hV hv₀ hgap hsmall hsep hsep' hn₀ hm₀
    have hd : 0 < gap / (4 * (1 + V)) := by positivity
    have hrad : 8 * r / (gap / (4 * (1 + V))) = 32 * (1 + V) * r / gap := by
      field_simp
      ring
    refine ⟨vel p₀, ?_⟩
    intro p hp
    obtain ⟨hv, hnp, hmp⟩ := hS p hp
    have hdia := strip_intersection_diameter hn hm hd hwedge hnp hmp hn₀ hm₀
    rwa [hrad] at hdia
  · exact ⟨0, fun p hp => (hnonempty ⟨p, hp⟩).elim⟩

/-- The strip intersection estimate pulled back to any original incidence
law. No measurability of the counted subset and no normalization are needed. -/
theorem unit_strip_overlap_charge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (vel : Ω → Plane) (S : Set Ω)
    {n m : Plane} {β γ r gap V : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hV : 0 ≤ V)
    (hgap : 0 < gap) (hsmall : 4 * r ≤ gap)
    (hsep : gap ≤ ‖n - m‖ + |β - γ|)
    (hsep' : gap ≤ ‖n + m‖ + |β + γ|)
    (hS : ∀ p ∈ S, ‖vel p‖ ≤ V ∧
      |inner ℝ (vel p) n - β| ≤ r ∧ |inner ℝ (vel p) m - γ| ≤ r)
    (B : ENNReal)
    (hcap : ∀ x : Plane, μ {p | dist (vel p) x ≤ 32 * (1 + V) * r / gap} ≤ B) :
    μ S ≤ B := by
  obtain ⟨center, hcenter⟩ := unit_strip_overlap_ball vel S hn hm hV hgap hsmall hsep hsep' hS
  exact (measure_mono hcenter).trans (hcap center)

/-- Candidate multiplicity is charged separately inside each original
parent. The reference budget remains a sum over the unchanged deeper laws. -/
theorem sum_parented_charges_le {Ω A D P : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype D] [DecidableEq P]
    (μ : D → Measure Ω) (parent : A → P) (ancestor : D → P)
    (S : A → D → Set Ω) (B : D → ENNReal) (C : ENNReal)
    (hcard : ∀ d, ((Finset.univ.filter (fun a => parent a = ancestor d)).card : ENNReal) ≤ C)
    (hzero : ∀ a d, parent a ≠ ancestor d → μ d (S a d) = 0)
    (hbound : ∀ a d, parent a = ancestor d → μ d (S a d) ≤ B d) :
    (∑ d, ∑ a, μ d (S a d)) ≤ C * ∑ d, B d := by
  classical
  have hdeep (d : D) : (∑ a, μ d (S a d)) ≤ C * B d := by
    have heq : (∑ a, μ d (S a d)) =
        ∑ a ∈ Finset.univ.filter (fun a => parent a = ancestor d), μ d (S a d) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      exact hzero a d (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha)
    rw [heq]
    calc
      _ ≤ ∑ _a ∈ Finset.univ.filter (fun a => parent a = ancestor d), B d :=
        Finset.sum_le_sum fun a ha => hbound a d (Finset.mem_filter.mp ha).2
      _ = ((Finset.univ.filter (fun a => parent a = ancestor d)).card : ENNReal) * B d := by
        simp [nsmul_eq_mul]
      _ ≤ C * B d := mul_le_mul' (hcard d) le_rfl
  calc
    _ ≤ ∑ d, C * B d := Finset.sum_le_sum fun d _ => hdeep d
    _ = _ := (Finset.mul_sum _ _ _).symm

end Submission.Obl.k4_finite_positive_mixed_cover_realization
