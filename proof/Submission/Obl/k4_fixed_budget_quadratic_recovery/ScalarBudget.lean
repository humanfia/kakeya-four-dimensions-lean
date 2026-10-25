/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/ScalarBudget.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarGreedy
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarFormat

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set
open Submission.Lib.K4FinitePlankAtlases

theorem scalarCandidateFloor_eq {N : ℝ} (hN : 0 < N) (c d s ε : ℝ) :
    scalarCandidateFloor N c d s ε = c * N ^ (-(d * s + 2 * ε)) := by
  rw [scalarCandidateFloor, ← Real.rpow_mul hN.le, mul_div_assoc,
    ← Real.rpow_sub hN, mul_assoc, ← Real.rpow_add hN]
  congr 2
  ring

/-- The greedy budget has the expected dimension exponent on the fixed
unit-prior normalization used in posterior recovery. -/
theorem scalar_greedy_count {N d s ε η n : ℝ} (hN : 0 < N)
    (h : n * scalarCandidateFloor N 1 d s ε ≤ N ^ η) :
    n ≤ N ^ (d * s + 2 * ε + η) := by
  rw [scalarCandidateFloor_eq hN, one_mul] at h
  have hp : 0 < N ^ (-(d * s + 2 * ε)) := Real.rpow_pos_of_pos hN _
  have hh := (le_div_iff₀ hp).mpr h
  rw [← Real.rpow_sub hN] at hh
  convert hh using 1
  congr 1
  ring

/-- A finite whole-block cover with a power count, fixed-degree disjoint
assignments, and ordinary coefficient bounds. All masses use the original law. -/
theorem finite_scalar_fit_cover
    (hmesh : ScalarMeshProjection)
    {d s m C S U ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ η : ℝ, η ≤ η₀ →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        (b : α → Fin 5 → ℝ),
        ScalarAdmissible N η d s m C S U 1 ν b μ →
        2 * N ^ (-η₀) ≤ μ.real univ →
        ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
          (A : Fin n → Set (Fin 5 → ℝ)),
          (n : ℝ) ≤ N ^ (d * s + 2 * ε + η) ∧
          (∀ i, (P i).totalDegree ≤ 2 ∧
            (∀ e, |(P i).coeff e| ≤ 240 * (N ^ ε) ^ 5) ∧
            MeasurableSet (A i) ∧ fmt 5 (n * 24) 4 (A i) ∧
            A i ⊆ scalarFit (P i) (N ^ ε * N ^ (-s))) ∧
          Pairwise (fun i j => Disjoint (A i) (A j)) ∧
          μ.real univ / 2 ≤ μ.real {p | ∃ i, b p.1 ∈ A i ∧ p.2 ∈ Icc (0 : ℝ) 1} := by
  obtain ⟨η₀, hη₀, N₀, hN₀, hgreedy⟩ :=
    scalar_greedy_half_coverage hmesh hd hd1 hs hsm hC hS hU hUm hε
  refine ⟨η₀, hη₀, N₀, hN₀, ?_⟩
  intro N hN η hη α _ ν μ b hadm hmass
  obtain ⟨l, hl, hcount, hcover⟩ := hgreedy N hN η hη α ν μ b 1 hadm hmass
  let P : Fin l.length → MvPolynomial (Fin 2) ℝ := fun i => (l.get i).P
  let F : Fin l.length → Set (Fin 5 → ℝ) :=
    fun i => scalarFit (P i) (N ^ ε * N ^ (-s))
  let A := firstAssignment F
  have hN1 : 1 ≤ N := by linarith
  have hdegree : ∀ i, (P i).totalDegree ≤ 2 := fun i => (l.get i).degree
  refine ⟨l.length, P, A, scalar_greedy_count (by linarith) hcount, ?_,
    firstAssignment_disjoint F, ?_⟩
  · intro i
    refine ⟨hdegree i, (l.get i).coeff_bound hN1 hε.le,
      measurableSet_firstAssignment F (fun j => (isClosed_scalarFit _ _).measurableSet) i,
      scalarFit_firstAssignment_format P hdegree _ i, fun _ hx => hx.1⟩
  · have heq : (⋃ Q ∈ l, Q.fit b) =
        {p | ∃ i, b p.1 ∈ A i ∧ p.2 ∈ Icc (0 : ℝ) 1} := by
      have hU := iUnion_firstAssignment F
      ext p
      simp only [mem_iUnion, ScalarCandidate.fit, mem_prod, mem_preimage,
        mem_ofPred_eq, exists_and_right, exists_prop]
      have hf : (∃ Q ∈ l, b p.1 ∈ scalarFit Q.P (N ^ ε * N ^ (-s))) ↔
          ∃ i, b p.1 ∈ F i := by
        constructor
        · rintro ⟨Q, hQ, hx⟩
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hQ
          exact ⟨i, hx⟩
        · rintro ⟨i, hx⟩
          exact ⟨l.get i, List.get_mem _ _, hx⟩
      rw [hf]
      apply and_congr_left
      intro _
      have hUA : (⋃ i, A i) = ⋃ i, F i := hU
      simpa only [mem_iUnion] using
        (show b p.1 ∈ (⋃ i, F i) ↔ b p.1 ∈ (⋃ i, A i) by rw [hUA])
    rwa [heq] at hcover

end Submission.Obl.k4_fixed_budget_quadratic_recovery
