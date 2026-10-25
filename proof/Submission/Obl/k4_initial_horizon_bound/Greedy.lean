import Mathlib

/-! Finite greedy removal with a positive lower bound on the mass removed.
The templates can form an infinite family. Each assignment is the entire
available part of the chosen template. -/

open MeasureTheory Set

namespace Submission.Obl.k4_initial_horizon_bound

variable {α β : Type*}

def greedyResidual (S : β → Set α) (U : Set α) : List β → Set α
  | [] => U
  | a :: as => greedyResidual S (U \ S a) as

def greedyPieces (S : β → Set α) (U : Set α) : List β → List (β × Set α)
  | [] => []
  | a :: as => (a, U ∩ S a) :: greedyPieces S (U \ S a) as

def GreedyEligible [MeasurableSpace α] (μ : Measure α) (S : β → Set α)
    (floor : β → ℝ) (U : Set α) : List β → Prop
  | [] => True
  | a :: as => floor a ≤ μ.real (U ∩ S a) ∧ GreedyEligible μ S floor (U \ S a) as

theorem greedyResidual_subset (S : β → Set α) (U : Set α) (as : List β) :
    greedyResidual S U as ⊆ U := by
  induction as generalizing U with
  | nil => exact Subset.rfl
  | cons a as ih => exact (ih _).trans sdiff_subset

theorem greedyResidual_eq (S : β → Set α) (U : Set α) (as : List β) :
    greedyResidual S U as = {x | x ∈ U ∧ ∀ a ∈ as, x ∉ S a} := by
  induction as generalizing U with
  | nil => ext x; simp [greedyResidual]
  | cons a as ih =>
    ext x
    simp only [greedyResidual, ih, mem_ofPred_eq, mem_sdiff, List.mem_cons,
      forall_eq_or_imp]
    tauto

theorem greedyPieces_length (S : β → Set α) (U : Set α) (as : List β) :
    (greedyPieces S U as).length = as.length := by
  induction as generalizing U with
  | nil => rfl
  | cons a as ih => simpa only [greedyPieces, List.length_cons] using congrArg Nat.succ (ih _)

theorem greedyPieces_subset (S : β → Set α) (U : Set α) (as : List β)
    (z : β × Set α) (hz : z ∈ greedyPieces S U as) : z.2 ⊆ U ∩ S z.1 := by
  induction as generalizing U with
  | nil => simp [greedyPieces] at hz
  | cons a as ih =>
    simp only [greedyPieces, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Subset.rfl
    · exact (ih _ hz).trans (inter_subset_inter_left _ sdiff_subset)

theorem greedyPieces_pairwise (S : β → Set α) (U : Set α) (as : List β) :
    (greedyPieces S U as).Pairwise (fun p q => Disjoint p.2 q.2) := by
  induction as generalizing U with
  | nil => simp [greedyPieces]
  | cons a as ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro z hz
    have hsub : z.2 ⊆ U \ S a := (greedyPieces_subset S (U \ S a) as z hz).trans
      inter_subset_left
    exact Set.disjoint_left.mpr fun x hx hx' => (hsub hx').2 hx.2

theorem measurableSet_greedyResidual [MeasurableSpace α] (S : β → Set α)
    (hS : ∀ a, MeasurableSet (S a)) {U : Set α} (hU : MeasurableSet U) (as : List β) :
    MeasurableSet (greedyResidual S U as) := by
  induction as generalizing U with
  | nil => exact hU
  | cons a as ih => exact ih (hU.diff (hS a))

theorem measurableSet_greedyPieces [MeasurableSpace α] (S : β → Set α)
    (hS : ∀ a, MeasurableSet (S a)) {U : Set α} (hU : MeasurableSet U) (as : List β)
    (z : β × Set α) (hz : z ∈ greedyPieces S U as) : MeasurableSet z.2 := by
  induction as generalizing U with
  | nil => simp [greedyPieces] at hz
  | cons a as ih =>
    simp only [greedyPieces, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hU.inter (hS a)
    · exact ih (hU.diff (hS a)) hz

theorem greedyPieces_floor [MeasurableSpace α] {μ : Measure α} {S : β → Set α}
    {floor : β → ℝ} {U : Set α} {as : List β} (h : GreedyEligible μ S floor U as)
    (z : β × Set α) (hz : z ∈ greedyPieces S U as) : floor z.1 ≤ μ.real z.2 := by
  induction as generalizing U with
  | nil => simp [greedyPieces] at hz
  | cons a as ih =>
    simp only [greedyPieces, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h.1
    · exact ih h.2 hz

/-- Exact bookkeeping for the unnormalized law, before any loss estimate. -/
theorem greedy_mass_identity [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : β → Set α) (hS : ∀ a, MeasurableSet (S a)) (U : Set α) (as : List β) :
    ((greedyPieces S U as).map (fun z => μ.real z.2)).sum +
      μ.real (greedyResidual S U as) = μ.real U := by
  induction as generalizing U with
  | nil => simp [greedyPieces, greedyResidual]
  | cons a as ih =>
    have hsplit : μ.real (U ∩ S a) + μ.real (U \ S a) = μ.real U :=
      measureReal_inter_add_sdiff (hS a)
    simpa only [greedyPieces, List.map_cons, List.sum_cons, greedyResidual, add_assoc,
      ih] using hsplit

/-- A positive uniform floor makes the greedy process terminate, even for
an infinite template family. At termination no remaining template is eligible. -/
theorem exists_greedy_packing [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : β → Set α) (hS : ∀ a, MeasurableSet (S a))
    (floor : β → ℝ) {δ : ℝ} (hδ : 0 < δ) (hfloor : ∀ a, δ ≤ floor a)
    (U : Set α) :
    ∃ as : List β, GreedyEligible μ S floor U as ∧
      ∀ a, μ.real (greedyResidual S U as ∩ S a) < floor a := by
  classical
  have aux (n : ℕ) : ∀ U : Set α, μ.real U < δ * n →
      ∃ as : List β, GreedyEligible μ S floor U as ∧
        ∀ a, μ.real (greedyResidual S U as ∩ S a) < floor a := by
    induction n with
    | zero =>
      intro U hU
      have hn := measureReal_nonneg (μ := μ) (s := U)
      simp only [Nat.cast_zero, mul_zero] at hU
      linarith
    | succ n ih =>
      intro U hU
      by_cases hstop : ∀ a, μ.real (U ∩ S a) < floor a
      · exact ⟨[], trivial, hstop⟩
      push Not at hstop
      obtain ⟨a, ha⟩ := hstop
      have hsplit : μ.real (U ∩ S a) + μ.real (U \ S a) = μ.real U :=
        measureReal_inter_add_sdiff (hS a)
      have hbound : μ.real (U \ S a) < δ * n := by
        rw [Nat.cast_succ] at hU
        have := hfloor a
        nlinarith
      obtain ⟨as, has, hstop⟩ := ih (U \ S a) hbound
      exact ⟨a :: as, ⟨ha, has⟩, hstop⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (μ.real U / δ)
  exact aux n U (by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn)

/-- The number of steps has the same quantitative bound as the usual
finite greedy argument: each step spends at least `δ` of the original mass. -/
theorem greedy_length_bound [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : β → Set α) (hS : ∀ a, MeasurableSet (S a))
    (floor : β → ℝ) {δ : ℝ} (hfloor : ∀ a, δ ≤ floor a)
    {U : Set α} {as : List β} (has : GreedyEligible μ S floor U as) :
    δ * (as.length : ℝ) + μ.real (greedyResidual S U as) ≤ μ.real U := by
  induction as generalizing U with
  | nil => simp [greedyResidual]
  | cons a as ih =>
    have hsplit : μ.real (U ∩ S a) + μ.real (U \ S a) = μ.real U :=
      measureReal_inter_add_sdiff (hS a)
    have htail := ih has.2
    have hstep := (hfloor a).trans has.1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, greedyResidual]
    nlinarith

/-- Analytic progress on every substantial residual gives disjoint charts
covering at least half of the original incidence mass. -/
theorem exists_greedy_half_cover [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : β → Set α) (hS : ∀ a, MeasurableSet (S a))
    (floor : β → ℝ) {δ : ℝ} (hδ : 0 < δ) (hfloor : ∀ a, δ ≤ floor a)
    (U : Set α)
    (hprogress : ∀ as : List β, GreedyEligible μ S floor U as →
      μ.real U / 2 < μ.real (greedyResidual S U as) →
      ∃ a, floor a ≤ μ.real (greedyResidual S U as ∩ S a)) :
    ∃ as : List β, GreedyEligible μ S floor U as ∧
      δ * (as.length : ℝ) ≤ μ.real U ∧
      μ.real U / 2 ≤ ((greedyPieces S U as).map (fun z => μ.real z.2)).sum ∧
      ∀ a, μ.real (greedyResidual S U as ∩ S a) < floor a := by
  obtain ⟨as, has, hstop⟩ := exists_greedy_packing μ S hS floor hδ hfloor U
  have hres : μ.real (greedyResidual S U as) ≤ μ.real U / 2 := by
    by_contra! hlarge
    obtain ⟨a, ha⟩ := hprogress as has hlarge
    exact (not_le_of_gt (hstop a)) ha
  have hlen := greedy_length_bound μ S hS floor hfloor has
  have hnonneg := measureReal_nonneg (μ := μ) (s := greedyResidual S U as)
  have hmass := greedy_mass_identity μ S hS U as
  refine ⟨as, has, ?_, ?_, hstop⟩ <;> linarith

end Submission.Obl.k4_initial_horizon_bound
