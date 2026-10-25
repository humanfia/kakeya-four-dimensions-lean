import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_significant_pair_bounds.Energy
import Submission.Obl.k4_oss_significant_pair_bounds.Scalar
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_significant_pair_bounds`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_significant_pair_bounds`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_significant_pair_bounds/`
belong to this obligation.
-/

theorem Submission.k4_oss_significant_pair_bounds : ∀ γ a : ℝ, 0 < γ → γ < 1 → 0 < a → 8 * a < γ → ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ Z : ℝ, 0 < Z → δ ^ (1 - γ) / 3 ≤ Z → ∀ A C : Finset ℝ, A.Nonempty → C.Nonempty → (∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y) → (∀ x ∈ C, ∀ y ∈ C, x ≠ y → δ ≤ dist x y) → ∀ q1 q2 : ℝ, 0 < q1 → 0 < q2 → (q1 * (A.card : ℝ) ≤ 1 ∧ q2 * (C.card : ℝ) ≤ 1 ∧ q1 ^ 2 * (A.card : ℝ) ≤ Z ∧ q2 ^ 2 * (C.card : ℝ) ≤ Z) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (δ ^ (2 * a) * Z) < ENNReal.ofReal (q1 ^ 2 * q2 ^ 2) * (MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product C).product (A.product C)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 16 * δ)).card : ℝ)))) → δ ^ (2 * a) ≤ q1 * (A.card : ℝ) ∧ δ ^ (2 * a) ≤ q2 * (C.card : ℝ) ∧ (A.card : ℝ) ≤ δ ^ (-1 + γ / 2) ∧ (C.card : ℝ) ≤ δ ^ (-1 + γ / 2) ∧ (A.card : ℝ) ≤ δ ^ (-3 * a) * (C.card : ℝ) ∧ (C.card : ℝ) ≤ δ ^ (-3 * a) * (A.card : ℝ) := by
  classical
  intro γ a hγ hγ1 ha hγa
  obtain ⟨r, hr, hr1, hcut⟩ :=
    Submission.Obl.k4_oss_significant_pair_bounds.exists_cutoff ha hγa
  refine ⟨r, hr, hr1, ?_⟩
  intro δ hδ hδr Z hZ hZlower A C hA hC hAsep hCsep q1 q2 hq1 hq2
    hcaps ν hνprob hν hlarge
  haveI : MeasureTheory.IsProbabilityMeasure ν := hνprob
  obtain ⟨hsmall, hcap, hratio⟩ := hcut δ hδ hδr
  have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hM : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hav := Submission.Obl.k4_oss_significant_pair_bounds.averaged_energy_le
    A C hδ hAsep hCsep ν hν
  have henergy : δ ^ (2 * a) * Z ≤
      129 * (q1 ^ 2 * (A.card : ℝ)) * (q2 ^ 2 * (C.card : ℝ)) *
        min (A.card : ℝ) (C.card : ℝ) := by
    have hlarge' : ENNReal.ofReal (δ ^ (2 * a) * Z) <
        ENNReal.ofReal (129 * (q1 ^ 2 * (A.card : ℝ)) *
          (q2 ^ 2 * (C.card : ℝ)) * min (A.card : ℝ) (C.card : ℝ)) := by
      calc
        _ < ENNReal.ofReal (q1 ^ 2 * q2 ^ 2) *
            (MeasureTheory.lintegral ν (fun t => ENNReal.ofReal
              (Submission.Obl.k4_oss_significant_pair_bounds.energy A C δ t))) := hlarge
        _ ≤ ENNReal.ofReal (q1 ^ 2 * q2 ^ 2) *
            ENNReal.ofReal (129 * (A.card : ℝ) * (C.card : ℝ) *
              min (A.card : ℝ) (C.card : ℝ)) := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hlarge').le
  have henergy' : δ ^ (2 * a) * Z ≤
      129 * (q2 ^ 2 * (C.card : ℝ)) * (q1 ^ 2 * (A.card : ℝ)) *
        min (C.card : ℝ) (A.card : ℝ) := by
    simpa only [min_comm, mul_left_comm, mul_assoc, mul_comm] using henergy
  obtain ⟨hmassA, hsizeA, hratioA⟩ :=
    Submission.Obl.k4_oss_significant_pair_bounds.power_bounds hδ hq1.le hq2.le
      hN hM hZ hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2
      hZlower hsmall hcap hratio henergy
  obtain ⟨hmassC, hsizeC, hratioC⟩ :=
    Submission.Obl.k4_oss_significant_pair_bounds.power_bounds hδ hq2.le hq1.le
      hM hN hZ hcaps.2.1 hcaps.1 hcaps.2.2.2 hcaps.2.2.1
      hZlower hsmall hcap hratio henergy'
  exact ⟨hmassA, hmassC, hsizeA, hsizeC, hratioA, hratioC⟩
