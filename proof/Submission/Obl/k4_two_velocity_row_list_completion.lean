import Mathlib
import ChallengeDeps
import Submission.Obl.k4_two_velocity_row_list_completion.Continuous
set_option linter.unusedVariables false

/-!
# `Submission.k4_two_velocity_row_list_completion`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_two_velocity_row_list_completion`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_two_velocity_row_list_completion/`
belong to this obligation.
-/

open MeasureTheory Set

namespace Submission.Obl.k4_two_velocity_row_list_completion

theorem _root_.Submission.k4_two_velocity_row_list_completion : ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (prior : MeasureTheory.Measure α) (active : MeasureTheory.Measure (α × ℝ)) (intercept velocity evaluation : α → ℝ) (row : α × ℝ → Fin 2 → ℝ) (palette : MeasureTheory.Measure ℝ) (error : ℝ) (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ), (fun (S a η N : ℝ) (α : Type) [MeasurableSpace α] (prior : MeasureTheory.Measure α) (active : MeasureTheory.Measure (α × ℝ)) (intercept velocity evaluation : α → ℝ) (row : α × ℝ → Fin 2 → ℝ) (palette : MeasureTheory.Measure ℝ) (error : ℝ) (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ) => (fun (ξ : ℝ) => (fun (position : α × ℝ → Fin 2 → ℤ) => Measurable intercept ∧ Measurable velocity ∧ Measurable evaluation ∧ Measurable row ∧ MeasureTheory.IsProbabilityMeasure prior ∧ MeasureTheory.IsProbabilityMeasure palette ∧ ξ ≤ error ∧ error ≤ 1 ∧ (∀ l, |intercept l| + |velocity l| ≤ N ^ η) ∧ active ≤ ENNReal.ofReal (N ^ η) • (prior.prod MeasureTheory.volume) ∧ active (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal (N ^ (-η)) ≤ active Set.univ ∧ (∀ x r : ℝ, ξ ≤ r → r ≤ 1 → palette (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) ∧ (∀ (q : Fin 2 → ℤ) (j : ℤ), active {p | position p = q ∧ ⌊velocity p.1 / ξ⌋ = j} ≤ ENNReal.ofReal (N ^ η * ξ ^ 2) * palette (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ))) ∧ (∀ᵐ p ∂active, (∀ j, |row p j| ≤ N ^ η) ∧ |row p 0 + velocity p.1 * row p 1 - evaluation p.1| ≤ N ^ η * error) ∧ (∀ (q : Fin 2 → ℤ) (j : ℤ), ((lists q j).card : ℝ) ≤ N ^ η) ∧ (∀ᵐ p ∂active, ⌊evaluation p.1 / error⌋ ∈ lists (position p) ⌊velocity p.1 / ξ⌋) ∧ (∀ (q r : Fin 2 → ℤ) (j : ℤ), active {p | position p = q ∧ (fun e => ⌊row p e / error⌋) = r ∧ ⌊velocity p.1 / ξ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * palette (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ)) * active {p | position p = q ∧ (fun e => ⌊row p e / error⌋) = r})) (fun p e => ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e / ξ⌋)) (N ^ (-a))) S a η N α prior active intercept velocity evaluation row palette error lists → ∃ bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ), (∀ q, ((bins q).card : ℝ) ≤ N ^ ε) ∧ ∀ᵐ p ∂active, (fun e => ⌊row p e / error⌋) ∈ bins (fun e => ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e / (N ^ (-a))⌋) := by
  intro S a ε hS ha hε
  obtain ⟨η, hη, hηε, N₀, hN₀, hscales⟩ := choose_scales S a ε hS ha hε
  refine ⟨η, hη, hηε, N₀, hN₀, ?_⟩
  intro N hN α inst prior active intercept velocity evaluation row palette error lists hyp
  rcases hyp with ⟨hintercept, hvelocity, hevaluation, hrowmeas, hprior, hpalette,
    hξE, hE1, htrajectory, hdomination, hsupport, hmass, hpalettecap, hjoint,
    hrow, hlistcard, hlists, hconditional⟩
  letI : MeasurableSpace α := inst
  letI : IsProbabilityMeasure prior := hprior
  letI : IsProbabilityMeasure palette := hpalette
  let K : ℝ := N ^ η
  let ξ : ℝ := N ^ (-a)
  let position (p : α × ℝ) : Fin 2 → ℤ := fun e =>
    ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e / ξ⌋
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hNpos : 0 < N := by linarith
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNpos _
  have hK : 1 ≤ K := Real.one_le_rpow (by linarith) hη.le
  obtain ⟨R, hR, hKR, hmesh, hRinv, hnear, hbudget⟩ := hscales N hN
  have hs : MeasurableSet ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hfinite : active univ ≤ ENNReal.ofReal K := by
    calc
      active univ = active (univ ×ˢ Icc (0 : ℝ) 1) := by
        rw [← measure_add_measure_compl hs, hsupport, add_zero]
      _ ≤ (ENNReal.ofReal K • prior.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
        hdomination _
      _ = ENNReal.ofReal K := by
        rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
        simp
  letI : IsFiniteMeasure active := ⟨hfinite.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨bins, hbins, haebins⟩ := continuous_completion active position
    (fun p => velocity p.1) (fun p => evaluation p.1) row palette lists
    hξ hξE hE1 hK hR hKR hmesh hnear
    (fun p => (le_add_of_nonneg_left (abs_nonneg (intercept p.1))).trans
      (htrajectory p.1)) hrow hlistcard hlists hpalettecap hconditional
  exact ⟨bins, fun q => (hbins q).trans hbudget, haebins⟩

end Submission.Obl.k4_two_velocity_row_list_completion
