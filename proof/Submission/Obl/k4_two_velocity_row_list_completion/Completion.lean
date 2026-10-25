import Submission.Obl.k4_two_velocity_row_list_completion.MeasureTable
import Submission.Obl.k4_two_velocity_row_list_completion.WeightedCount

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

/-- Compatibility is witnessed by an actual good incidence in the indicated state. -/
def Compatible {Ω Q R V : Type*} (position : Ω → Q) (row : Ω → R) (code : Ω → V)
    (good : Ω → Prop) (q : Q) (r : R) (j : V) : Prop :=
  ∃ p, good p ∧ position p = q ∧ row p = r ∧ code p = j

/-- An abstract completion of countable row states from the original conditional caps.
The geometric input only counts states compatible with two separated velocities. -/
theorem complete_row_states {Ω Q R V : Type*} [MeasurableSpace Ω]
    [Countable Q] [Countable R] (μ : Measure Ω) [IsFiniteMeasure μ]
    (position : Ω → Q) (row : Ω → R) (code : Ω → V) (good : Ω → Prop)
    (allowed : Finset R) (velocities : Finset V) (weight center : V → ℝ)
    {K B δ : ℝ} (hK : 0 < K) (hB : 0 ≤ B)
    (hw : ∀ j ∈ velocities, 0 ≤ weight j)
    (hw1 : (∑ j ∈ velocities, weight j) ≤ 1)
    (hcode : ∀ p, code p ∈ velocities)
    (hgood : ∀ᵐ p ∂μ, good p) (hallowed : ∀ᵐ p ∂μ, row p ∈ allowed)
    (hcap : ∀ q r j, j ∈ velocities →
      μ {p | position p = q ∧ row p = r ∧ code p = j} ≤
        ENNReal.ofReal K * ENNReal.ofReal (weight j) *
          μ {p | position p = q ∧ row p = r})
    (hnear : ∀ j ∈ velocities,
      (∑ k ∈ velocities, if |center k - center j| < δ then weight k else 0) ≤
        (1 / K) / 2)
    (hpairs : ∀ q j, j ∈ velocities → ∀ k, k ∈ velocities →
      δ ≤ |center k - center j| →
      ((allowed.filter (fun r => Compatible position row code good q r j ∧
        Compatible position row code good q r k)).card : ℝ) ≤ B) :
    ∃ bins : Q → Finset R,
      (∀ q, ((bins q).card : ℝ) ≤ 2 * K ^ 2 * B) ∧
      ∀ᵐ p ∂μ, row p ∈ bins (position p) := by
  let bins := positiveStates μ position row allowed
  refine ⟨bins, ?_, ae_mem_positiveStates μ position row allowed hallowed⟩
  intro q
  have hdeg (r : R) (hr : r ∈ bins q) :
      1 / K ≤ ∑ j ∈ velocities,
        if Compatible position row code good q r j then weight j else 0 := by
    exact degree_of_conditional_cap μ position row code good velocities weight hK hw
      hcode hgood q r (Finset.mem_filter.mp hr).2 (hcap q r)
  have hfiber (j : V) (hj : j ∈ velocities) (k : V) (hk : k ∈ velocities)
      (hsep : δ ≤ |center k - center j|) :
      (((bins q).filter (fun r => Compatible position row code good q r j ∧
        Compatible position row code good q r k)).card : ℝ) ≤ B := by
    refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hpairs q j hj k hk hsep)
    intro r hr
    obtain ⟨hr, hcompat⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, hcompat⟩
  have hcount := weighted_pair_count (bins q) velocities weight center
    (Compatible position row code good q) (1 / K) B δ
    (by positivity) hB hw hw1 hdeg hnear hfiber
  have hmul := mul_le_mul_of_nonneg_right hcount (sq_nonneg K)
  have hcancel : (1 / K) ^ 2 * K ^ 2 = 1 := by field_simp
  nlinarith [hcancel]

end Submission.Obl.k4_two_velocity_row_list_completion
