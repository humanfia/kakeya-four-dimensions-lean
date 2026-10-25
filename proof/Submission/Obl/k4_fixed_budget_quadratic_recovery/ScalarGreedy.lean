/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/ScalarGreedy.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set Filter
open Submission.Lib.K4FinitePlankAtlases

theorem scalarCandidateFloor_pos {N c d s ε : ℝ} (hN : 0 < N) (hc : 0 < c) :
    0 < scalarCandidateFloor N c d s ε := by
  unfold scalarCandidateFloor
  positivity

/-- The number of insertions is charged to the unchanged original mass
budget, rather than to the success-normalized residual. -/
theorem greedy_length_budget {X β : Type*} [MeasurableSpace X]
    (F : β → Set X) (hF : ∀ b, MeasurableSet (F b)) {η : ℝ}
    {μ : Measure X} [IsFiniteMeasure μ] {l : List β}
    (h : GreedySequence F η μ l) : (l.length : ℝ) * η ≤ μ.real univ := by
  induction l generalizing μ with
  | nil => simp only [List.length_nil, Nat.cast_zero, zero_mul]; exact ENNReal.toReal_nonneg
  | cons b l ih =>
    cases h with
    | cons hb ht =>
      have hi := ih ht
      rw [measureReal_restrict_apply_univ, measureReal_compl (hF b)] at hi
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem greedy_covered_mass {X β : Type*} [MeasurableSpace X]
    (F : β → Set X) (hF : ∀ b, MeasurableSet (F b))
    (μ : Measure X) [IsFiniteMeasure μ] (l : List β) :
    μ.real (⋃ b ∈ l, F b) = μ.real univ - (residualMeasure F μ l).real univ := by
  have hU : MeasurableSet (⋃ b ∈ l, F b) :=
    MeasurableSet.biUnion l.finite_toSet.countable (fun b _ => hF b)
  rw [residualMeasure_eq F hF, measureReal_restrict_apply_univ, measureReal_compl hU]
  ring

theorem greedy_half_coverage {X β : Type*} [MeasurableSpace X]
    (F : β → Set X) (hF : ∀ b, MeasurableSet (F b))
    (μ : Measure X) [IsFiniteMeasure μ] (l : List β) {e : ℝ}
    (hres : (residualMeasure F μ l).real univ ≤ e) (hfloor : 2 * e ≤ μ.real univ) :
    μ.real univ / 2 ≤ μ.real (⋃ b ∈ l, F b) := by
  rw [greedy_covered_mass F hF μ l]
  linarith

/-- Maximal whole-block fits leave only the fixed power-small residual
allowed by the scalar theorem. Every insertion uses the original law,
with earlier fits deleted and without any renormalization. -/
theorem scalar_greedy_coverage
    (hmesh : ScalarMeshProjection)
    {d s m C S U ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (ν : Measure α) (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
        (b : α → Fin 5 → ℝ) (c : ℝ),
        ScalarAdmissible N η d s m C S U c ν b μ →
        ∃ l : List (ScalarCandidate N s m ε),
          GreedySequence (fun F => F.fit b) (scalarCandidateFloor N c d s ε) μ l ∧
          (residualMeasure (fun F => F.fit b) μ l).real univ < N ^ (-η) := by
  obtain ⟨η, hη, N₀, hN₀, hcandidate⟩ :=
    scalar_candidate_of_mesh hmesh hd hd1 hs hsm hC hS hU hUm hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν μ _ b c hadm
  have hNpos : 0 < N := by linarith
  have hc : 0 < c := (Real.rpow_pos_of_pos hNpos _).trans_le hadm.2.2.2.2.2.1
  have hfloor := scalarCandidateFloor_pos (d := d) (s := s) (ε := ε) hNpos hc
  let F : ScalarCandidate N s m ε → Set (α × ℝ) := fun P => P.fit b
  have hF : ∀ P, MeasurableSet (F P) := fun P => P.measurable_fit hadm.1
  obtain ⟨l, hl, hstop⟩ := exists_greedy_exhaustion F hF μ hfloor
  refine ⟨l, hl, ?_⟩
  rw [residualMeasure_eq F hF μ l] at hstop ⊢
  let μr := μ.restrict (⋃ P ∈ l, F P)ᶜ
  have hμr : μr ≤ μ := Measure.restrict_le_self
  have hadmr := hadm.mono hμr
  by_contra hsmall
  have hmass : ENNReal.ofReal (N ^ (-η)) ≤ μr univ := by
    apply (ENNReal.ofReal_le_ofReal (le_of_not_gt hsmall)).trans
    simp only [measureReal_def]
    exact le_of_eq (ENNReal.ofReal_toReal (measure_ne_top μr univ))
  obtain ⟨P, hP⟩ := hcandidate N hN α ν μr b c hadmr hmass
  have hPreal : scalarCandidateFloor N c d s ε ≤ μr.real (F P) := by
    have h := ENNReal.toReal_mono (measure_ne_top μr _) hP
    simpa only [ENNReal.toReal_ofReal hfloor.le, measureReal_def, F] using h
  exact (not_le_of_gt (hstop P)) hPreal

/-- A stronger external mass floor turns the fixed residual cutoff into
half coverage and a polynomial insertion count. The external loss may
be chosen after the internal scalar cutoff. -/
theorem scalar_greedy_half_coverage
    (hmesh : ScalarMeshProjection)
    {d s m C S U ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ η : ℝ, η ≤ η₀ →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        (b : α → Fin 5 → ℝ) (c : ℝ),
        ScalarAdmissible N η d s m C S U c ν b μ →
        2 * N ^ (-η₀) ≤ μ.real univ →
        ∃ l : List (ScalarCandidate N s m ε),
          GreedySequence (fun F => F.fit b) (scalarCandidateFloor N c d s ε) μ l ∧
          (l.length : ℝ) * scalarCandidateFloor N c d s ε ≤ N ^ η ∧
          μ.real univ / 2 ≤ μ.real (⋃ F ∈ l, F.fit b) := by
  obtain ⟨η₀, hη₀, N₀, hN₀, hgreedy⟩ :=
    scalar_greedy_coverage hmesh hd hd1 hs hsm hC hS hU hUm hε
  refine ⟨η₀, hη₀, N₀, hN₀, ?_⟩
  intro N hN η hη α _ ν μ b c hadm hmass
  have hN1 : 1 ≤ N := by linarith
  have := hadm.isFiniteMeasure
  obtain ⟨l, hl, hres⟩ := hgreedy N hN α ν μ b c (hadm.mono_loss hN1 hη)
  have htotal : μ.real univ ≤ N ^ η := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hadm.total_mass_le
    simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (zero_le_one.trans hN1) η)] using h
  refine ⟨l, hl, ?_, ?_⟩
  · exact (greedy_length_budget _ (fun F => F.measurable_fit hadm.1) hl).trans htotal
  · exact greedy_half_coverage _ (fun F => F.measurable_fit hadm.1) μ l hres.le hmass

end Submission.Obl.k4_fixed_budget_quadratic_recovery
