import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Lib.K4MeshListRecovery.MeasurableLists

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Set

/-- The three adjacent integer bins in each of the six coefficient coordinates. -/
def binCube (q : Fin 6 → ℤ) : Finset (Fin 6 → ℤ) :=
  Fintype.piFinset (fun j => Finset.Icc (q j - 1) (q j + 1))

theorem binCube_card (q : Fin 6 → ℤ) : (binCube q).card = 3 ^ 6 := by
  rw [binCube, Fintype.card_piFinset]
  have hc (j : Fin 6) : (Finset.Icc (q j - 1) (q j + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  simp_rw [hc]
  norm_num

def binNeighborIndices {β : Type*} [Fintype β] (code : β → Fin 6 → ℤ) (b : β) :
    Finset β := Finset.univ.filter (fun a => code a ∈ binCube (code b))

/-- Coefficients within one bin width have integer codes in adjacent bins. -/
theorem floor_codes_mem_binCube {ρ : ℝ} (hρ : 0 < ρ)
    {c c' : Fin 6 → ℝ} (hc : ∀ j, |c j - c' j| ≤ ρ) :
    (fun j => ⌊c j / ρ⌋) ∈ binCube (fun j => ⌊c' j / ρ⌋) := by
  rw [binCube, Fintype.mem_piFinset]
  intro j
  have hdiv : |c j / ρ - c' j / ρ| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hρ]
    exact (div_le_one hρ).mpr (hc j)
  have hh := abs_floor_sub_lt (c j / ρ) (c' j / ρ)
  have hcast : |((⌊c j / ρ⌋ - ⌊c' j / ρ⌋ : ℤ) : ℝ)| < (2 : ℝ) := by linarith
  have hint : |⌊c j / ρ⌋ - ⌊c' j / ρ⌋| < (2 : ℤ) := by exact_mod_cast hcast
  rw [abs_lt] at hint
  simp only [Finset.mem_Icc]
  omega

/-- Maximizing a neighbor score selects a measurable list of coefficient bins.
Repeated original bin codes do not increase its size. -/
theorem exists_measurable_bin_lists
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (π : X → β → ℝ) (hπmeas : ∀ a, Measurable (fun x => π x a))
    (hπnonneg : ∀ x a, 0 ≤ π x a) (hπmass : ∀ x, ∑ a, π x a ≤ 1)
    (code : β → Fin 6 → ℤ) :
    ∃ L : X → Finset (Fin 6 → ℤ),
      (∀ q, MeasurableSet {x | q ∈ L x}) ∧ (∀ x, (L x).card ≤ 3 ^ 6) ∧
      ∀ x, (∑ b, π x b * ∑ a ∈ binNeighborIndices code b, π x a) ≤
        ∑ a ∈ Finset.univ.filter (fun a => code a ∈ L x), π x a := by
  classical
  cases isEmpty_or_nonempty β with
  | inl h =>
    exact ⟨fun _ => ∅, fun q => by simp, fun _ => by simp, fun x => by simp⟩
  | inr h =>
    let score : β → X → ℝ := fun b x => ∑ a ∈ binNeighborIndices code b, π x a
    have hscore : ∀ b, Measurable (score b) := fun b => by fun_prop
    obtain ⟨select, hselect, hmax⟩ :=
      Submission.Lib.K4MeshListRecovery.exists_measurable_finite_argmax score hscore
    let L : X → Finset (Fin 6 → ℤ) := fun x => binCube (code (select x))
    refine ⟨L, ?_, fun x => (binCube_card _).le, ?_⟩
    · intro q
      have hU := (Finset.univ.filter (fun b => q ∈ binCube (code b))).measurableSet_biUnion
        (fun b _ => hselect b)
      convert hU using 1
      ext x
      simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_ofPred_eq]
      constructor
      · intro hx
        exact ⟨select x, hx, rfl⟩
      · rintro ⟨b, hb, heq⟩
        simpa only [L, heq] using hb
    · intro x
      have hsnonneg : 0 ≤ score (select x) x :=
        Finset.sum_nonneg (fun a _ => hπnonneg x a)
      calc
        _ ≤ ∑ b, π x b * score (select x) x := by
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left (hmax x b) (hπnonneg x b)
        _ = (∑ b, π x b) * score (select x) x := by rw [Finset.sum_mul]
        _ ≤ 1 * score (select x) x :=
          mul_le_mul_of_nonneg_right (hπmass x) hsnonneg
        _ = _ := by simp only [one_mul]; rfl

end Submission.Obl.k4_fixed_budget_quadratic_recovery
