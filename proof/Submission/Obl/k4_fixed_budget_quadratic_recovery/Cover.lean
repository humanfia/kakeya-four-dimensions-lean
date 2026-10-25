import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarBudget
import Submission.Obl.k4_fixed_budget_quadratic_recovery.RecoveryInterface

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set
open Submission.Lib.K4FinitePlankAtlases

/-- Priority assignment identifies the complete union of the chosen geometric fits. -/
theorem scalarCandidate_union_priority {α : Type} [MeasurableSpace α]
    {N s m δ : ℝ} (l : List (ScalarCandidate N s m δ)) (b : α → Fin 5 → ℝ) :
    (⋃ Q ∈ l, Q.fit b) =
      {p | (∃ i : Fin l.length, b p.1 ∈ firstAssignment
        (fun j : Fin l.length => scalarFit (l.get j).P (N ^ δ * N ^ (-s))) i) ∧
        p.2 ∈ Icc (0 : ℝ) 1} := by
  let F : Fin l.length → Set (Fin 5 → ℝ) :=
    fun i => scalarFit (l.get i).P (N ^ δ * N ^ (-s))
  have hU := iUnion_firstAssignment F
  ext p
  simp only [mem_iUnion, ScalarCandidate.fit, mem_prod, mem_preimage,
    mem_ofPred_eq, exists_and_right, exists_prop]
  have hf : (∃ Q ∈ l, b p.1 ∈ scalarFit Q.P (N ^ δ * N ^ (-s))) ↔
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
  simpa only [mem_iUnion] using
    (show b p.1 ∈ (⋃ i, F i) ↔ b p.1 ∈ (⋃ i, firstAssignment F i) by rw [hU])

/-- The scalar mesh input supplies a geometric atlas with an explicit residual cutoff.
The input loss may be smaller than the mesh theorem's admissibility exponent. -/
theorem finite_scalar_fit_cover_residual
    (hmesh : ScalarMeshProjection)
    {d s m S U δ : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ η : ℝ, η ≤ η₀ →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        (b : α → Fin 5 → ℝ),
        ScalarAdmissible N η d s m 1 S U 1 ν b μ →
        ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
          (A : Fin n → Set (Fin 5 → ℝ)),
          (n : ℝ) ≤ N ^ (d * s + 2 * δ + η) ∧
          (∀ i, (P i).totalDegree ≤ 2 ∧
            (∀ e, |(P i).coeff e| ≤ 240 * (N ^ δ) ^ 5) ∧
            MeasurableSet (A i) ∧ fmt 5 (n * 24) 4 (A i) ∧
            A i ⊆ scalarFit (P i) (N ^ δ * N ^ (-s))) ∧
          Pairwise (fun i j => Disjoint (A i) (A j)) ∧
          μ.real {p | ¬ ∃ i, b p.1 ∈ A i} < N ^ (-η₀) := by
  obtain ⟨η₀, hη₀, N₀, hN₀, hgreedy⟩ :=
    scalar_greedy_coverage (C := 1) hmesh hd hd1 hs hsm (by norm_num) hS hU hUm hδ
  refine ⟨η₀, hη₀, N₀, hN₀, ?_⟩
  intro N hN η hη α _ ν μ b hadm
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have := hadm.isFiniteMeasure
  obtain ⟨l, hl, hres⟩ := hgreedy N hN α ν μ b 1 (hadm.mono_loss hN1 hη)
  let P : Fin l.length → MvPolynomial (Fin 2) ℝ := fun i => (l.get i).P
  let F : Fin l.length → Set (Fin 5 → ℝ) :=
    fun i => scalarFit (P i) (N ^ δ * N ^ (-s))
  let A := firstAssignment F
  have htotal : μ.real univ ≤ N ^ η := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hadm.total_mass_le
    simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le η)] using h
  have hcount : (l.length : ℝ) * scalarCandidateFloor N 1 d s δ ≤ N ^ η :=
    (greedy_length_budget _ (fun Q => Q.measurable_fit hadm.1) hl).trans htotal
  have hdegree : ∀ i, (P i).totalDegree ≤ 2 := fun i => (l.get i).degree
  refine ⟨l.length, P, A, scalar_greedy_count hNpos hcount, ?_,
    firstAssignment_disjoint F, ?_⟩
  · intro i
    exact ⟨hdegree i, (l.get i).coeff_bound hN1 hδ.le,
      measurableSet_firstAssignment F (fun j => (isClosed_scalarFit _ _).measurableSet) i,
      scalarFit_firstAssignment_format P hdegree _ i, fun _ hx => hx.1⟩
  · rw [residualMeasure_eq _ (fun Q => Q.measurable_fit hadm.1),
      measureReal_restrict_apply_univ] at hres
    apply lt_of_le_of_lt (measureReal_mono ?_) hres
    rw [scalarCandidate_union_priority l b]
    intro p hp
    exact fun h => hp h.1

end Submission.Obl.k4_fixed_budget_quadratic_recovery
