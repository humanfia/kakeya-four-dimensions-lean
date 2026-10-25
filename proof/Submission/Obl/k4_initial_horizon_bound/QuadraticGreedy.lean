import Submission.Obl.k4_initial_horizon_bound.Greedy

/-! A quadratic prior cap supplies the positive mass floor for greedy
selection. In particular, no arbitrary lower width cutoff is needed. -/

open MeasureTheory Set

namespace Submission.Obl.k4_initial_horizon_bound

variable {α β γ : Type*}

theorem greedyResidual_map (S : β → Set α) (f : γ → β) (U : Set α) (as : List γ) :
    greedyResidual S U (as.map f) = greedyResidual (S ∘ f) U as := by
  induction as generalizing U with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.map_cons, greedyResidual, Function.comp_apply] using ih (U \ S (f a))

theorem greedyEligible_map [MeasurableSpace α] (μ : Measure α)
    (S : β → Set α) (floor : β → ℝ) (f : γ → β) (U : Set α) (as : List γ) :
    GreedyEligible μ S floor U (as.map f) ↔
      GreedyEligible μ (S ∘ f) (floor ∘ f) U as := by
  induction as generalizing U with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, GreedyEligible, Function.comp_apply, ih]

/-- A cap quadratic in plank area makes each eligible linear-in-area
removal cost at least `a^2/B`, uniformly over the continuous plank family. -/
theorem exists_quadratic_greedy_packing [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (S : β → Set α) (hS : ∀ b, MeasurableSet (S b)) (size : β → ℝ)
    (hsize : ∀ b, 0 ≤ size b) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hcap : ∀ b, μ.real (S b) ≤ B * (size b) ^ 2) (U : Set α) :
    ∃ as : List β, GreedyEligible μ S (fun b => a * size b) U as ∧
      (a ^ 2 / B) * (as.length : ℝ) ≤ μ.real U ∧
      ∀ b, μ.real (greedyResidual S U as ∩ S b) ≤ a * size b := by
  classical
  let Good := {b : β // a / B ≤ size b}
  let S' : Good → Set α := fun b => S b
  let floor : Good → ℝ := fun b => a * size b
  have hfloor (b : Good) : a ^ 2 / B ≤ floor b := by
    have h := mul_le_mul_of_nonneg_left b.property ha.le
    dsimp [floor]
    convert h using 1 <;> ring
  obtain ⟨as, has, hstop⟩ := exists_greedy_packing μ S' (fun b => hS b) floor
    (div_pos (sq_pos_of_pos ha) hB) hfloor U
  let bs : List β := as.map Subtype.val
  have hbs : GreedyEligible μ S (fun b => a * size b) U bs :=
    (greedyEligible_map μ S (fun b => a * size b) Subtype.val U as).mpr has
  refine ⟨bs, hbs, ?_, ?_⟩
  · have h := greedy_length_bound μ S' (fun b => hS b) floor hfloor has
    have hn := measureReal_nonneg (μ := μ) (s := greedyResidual S' U as)
    simp only [bs, List.length_map]
    linarith
  · intro b
    by_cases hb : a / B ≤ size b
    · have h := (hstop ⟨b, hb⟩).le
      simpa only [bs, greedyResidual_map, S', floor, Function.comp_def] using h
    · have hsmall : B * size b ≤ a := by
        have h := (lt_div_iff₀ hB).mp (lt_of_not_ge hb)
        simpa only [mul_comm] using h.le
      calc
        _ ≤ μ.real (S b) := measureReal_mono inter_subset_right
        _ ≤ B * (size b) ^ 2 := hcap b
        _ ≤ a * size b := by nlinarith [hsize b]

end Submission.Obl.k4_initial_horizon_bound
