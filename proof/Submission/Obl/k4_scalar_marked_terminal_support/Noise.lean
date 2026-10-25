import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure

namespace Submission.Obl.k4_scalar_marked_terminal_support

open MeasureTheory Set
open scoped ENNReal

open Submission.Obl.k4_scalar_marked_packet_recovery
  (Noise MarkedPrior MarkedEvent MarkedLaw timeCell noise_ae_cube measurableSet_markedEvent)

lemma noisyPrior_ae {σ : ℝ} (hσ : 0 < σ) {H : ℕ} (b₀ : Fin H → (Fin 5 → ℝ))
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : (ℕ × (Fin 5 → ℝ)) → Prop) (hP : MeasurableSet {p | P p})
    (h : ∀ j, 0 < w j → ∀ u, (∀ i, u i ∈ Icc 0 σ) → P ((j : ℕ), b₀ j + u)) :
    ∀ᵐ p ∂∑ j, ENNReal.ofReal (w j) •
      (Noise σ).map (fun u => ((j : ℕ), b₀ j + u)), P p := by
  classical
  apply ae_finsetSum_measure_iff.mpr
  intro j _
  by_cases hj : w j = 0
  · simp [hj]
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) hP).mpr
    filter_upwards [noise_ae_cube hσ] with u hu
    exact h j (lt_of_le_of_ne (hw j) (Ne.symm hj)) u hu

lemma noisyPrior_ae_coordinates {σ : ℝ} (hσ : 0 < σ) {H : ℕ} (b₀ : Fin H → (Fin 5 → ℝ))
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∀ᵐ p ∂∑ j, ENNReal.ofReal (w j) •
      (Noise σ).map (fun u => ((j : ℕ), b₀ j + u)),
      ∃ j : Fin H, 0 < w j ∧ p.1 = (j : ℕ) ∧ ∀ i, p.2 i - b₀ j i ∈ Icc 0 σ := by
  apply noisyPrior_ae hσ b₀ w hw
  · simp only [ofPred_exists]
    refine MeasurableSet.iUnion (fun j : Fin H => ?_)
    simp only [ofPred_and]
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (measurableSet_eq_fun measurable_fst measurable_const) ?_
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop))
  · intro j hj u hu
    refine ⟨j, hj, rfl, ?_⟩
    intro i
    simpa using hu i

lemma noisyMarkedLaw_ae {σ : ℝ} (hσ : 0 < σ) {H J : ℕ}
    (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool)
    (hw : ∀ j, 0 ≤ w j) (P : ((ℕ × (Fin 5 → ℝ)) × ℝ) → Prop)
    (h : ∀ j, 0 < w j → ∀ c : Fin 5 → ℝ, (∀ i, c i - b₀ j i ∈ Icc 0 σ) →
      ∀ z : Fin J, mark j z = true → ∀ t ∈ timeCell J z, P (((j : ℕ), c), t)) :
    ∀ᵐ p ∂MarkedLaw σ H J b₀ w mark, P p := by
  have hp := noisyPrior_ae_coordinates hσ b₀ w hw
  have hp' := (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure ℝ))).tendsto_ae.eventually hp
  filter_upwards [ae_restrict_of_ae hp', ae_restrict_mem (measurableSet_markedEvent mark)]
    with p hp he
  obtain ⟨j, hj, htag, hc⟩ := hp
  obtain ⟨j', hj', z, hm, ht⟩ := he
  have hjeq : j' = j := Fin.ext (hj'.symm.trans htag)
  subst j'
  have heq : p = (((j : ℕ), p.1.2), p.2) := by
    rcases p with ⟨⟨n, c⟩, t⟩
    simp only [Prod.mk.injEq, and_true, and_self] at htag ⊢
    exact htag
  rw [heq]
  exact h j hj _ hc z hm _ ht

end Submission.Obl.k4_scalar_marked_terminal_support
