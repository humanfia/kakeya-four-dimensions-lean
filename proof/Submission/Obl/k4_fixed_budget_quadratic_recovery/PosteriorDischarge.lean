import Submission.Obl.k4_fixed_budget_quadratic_recovery.SeparatedPairs
import Submission.Obl.k4_fixed_budget_quadratic_recovery.BinRecovery
import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorInterface

/-!
# The finite posterior consequence holds

`PosteriorBinRecovery` follows from the separated-pair bound
(`separated_component_pair_mass`, from the accepted two-colour matching
theorem) and the component-level bin lists (`recover_component_bin_lists`):
pairs of tests whose coefficients differ by more than the bin width are
separated on the base box, so their unnormalized posterior-pair mass is at most
the matching loss.
-/

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Set
open scoped ENNReal

section Discharge

variable {Obs : Type*} [MeasurableSpace Obs]

/-- The posterior-pair law of an event depending only on the pair of indices is
the sum of the corresponding component pair masses. -/
theorem posteriorPairLaw_indexEvent {n : ℕ} (comp : Fin n → Measure Obs)
    (P : Fin n × Fin n → Prop) [DecidablePred P] :
    posteriorPairLaw (∑ k, comp k) (componentPosterior comp) {p | P p.1} =
      ∑ ι : Fin n × Fin n, if P ι then componentPairLaw comp ι univ else 0 := by
  have hS : MeasurableSet {p : (Fin n × Fin n) × Obs | P p.1} :=
    measurable_fst (Set.toFinite {ι : Fin n × Fin n | P ι}).measurableSet
  unfold posteriorPairLaw
  rw [Measure.finsetSum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro b' _
  rw [Measure.map_apply (by fun_prop) hS]
  by_cases h : P (b, b')
  · have hpre : (fun x : Obs => ((b, b'), x)) ⁻¹' {p | P p.1} = univ := by
      ext x
      simp [h]
    rw [hpre, if_pos h]
    rfl
  · have hpre : (fun x : Obs => ((b, b'), x)) ⁻¹' {p | P p.1} = ∅ := by
      ext x
      simp [h]
    rw [hpre, if_neg h, measure_empty]

end Discharge

/-- Tests whose coefficients differ by more than eight times the separation
level are separated on the base box. -/
theorem separatedPair_of_coeff_gap {n : ℕ} {F : Fin n → Fin 6 → ℝ} {Y r ρ : ℝ}
    (hY : 1 ≤ Y) (hrρ : 8 * r ≤ ρ) {ι : Fin n × Fin n}
    (h : ∃ a, ρ < |F ι.1 a - F ι.2 a|) : SeparatedPair F Y r ι := by
  by_contra hsep
  obtain ⟨a, ha⟩ := h
  have hval : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |quadraticValue (F ι.1 - F ι.2) t z| ≤ r := by
    intro t ht z hz
    have hw : (t, z) ∈ baseBox Y := ⟨ht, ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hlt : ¬ r ≤ |quadraticValue (F ι.1) t z - quadraticValue (F ι.2) t z| :=
      fun hle => hsep ⟨(t, z), hw, hle⟩
    have heq : quadraticValue (F ι.1 - F ι.2) t z =
        quadraticValue (F ι.1) t z - quadraticValue (F ι.2) t z := by
      simp only [quadraticValue, Pi.sub_apply]
      ring
    rw [heq]
    exact (lt_of_not_ge hlt).le
  have hcoef := quadratic_coefficients_bound hval a
  simp only [Pi.sub_apply] at hcoef
  linarith

/-- **The finite posterior consequence used by the scalar assembly holds.** -/
theorem posteriorBinRecovery_holds : PosteriorBinRecovery := by
  intro d hd hd1
  obtain ⟨e, he, R₀, hR₀, hsep⟩ :=
    separated_component_pair_mass (Obs := EuclideanSpace ℝ (Fin 3) × ℤ) hd hd1
  refine ⟨e, he, R₀, hR₀, ?_⟩
  intro R hR n comp hcomp base signal F Y H τ K ρ hbase hsignal hY hK hH hρ hnR hF hFY hτ hρR
    hagree hmarg
  have hR0 : 0 < R := by linarith
  have hagree' : ∀ i, ∀ᵐ o ∂comp i, base o ∈ baseBox Y ∧
      |signal o - quadraticValue (F i) (base o).1 (base o).2| ≤ τ := by
    intro i
    filter_upwards [hagree i] with o ho
    obtain ⟨h1, h2, h3⟩ := ho
    exact ⟨⟨h1, abs_le.mp h2⟩, h3⟩
  have hbad := hsep R hR n comp hcomp base signal F Y H τ K hbase hsignal hY hK hH hnR hF hFY hτ
    hagree' hmarg
  have h8 : 8 * R ^ (-e) ≤ ρ := by
    have := Real.rpow_pos_of_pos hR0 (-e)
    linarith
  classical
  have hbadP : posteriorPairLaw (∑ i, comp i) (componentPosterior comp)
      {p | ∃ a : Fin 6, ρ < |F p.1.1 a - F p.1.2 a|} ≤
      ENNReal.ofReal (n * K * (2 * Y) * R ^ (-2 * e)) := by
    rw [posteriorPairLaw_indexEvent comp (fun ι => ∃ a : Fin 6, ρ < |F ι.1 a - F ι.2 a|)]
    refine (Finset.sum_le_sum fun ι _ => ?_).trans hbad
    by_cases hgap : ∃ a : Fin 6, ρ < |F ι.1 a - F ι.2 a|
    · rw [if_pos hgap, if_pos (separatedPair_of_coeff_gap hY h8 hgap)]
    · rw [if_neg hgap]
      exact zero_le
  obtain ⟨L, hLm, hLc, hL⟩ := recover_component_bin_lists comp F hρ
    (by positivity) hbadP
  refine ⟨L, hLm, hLc, ?_⟩
  have htot : (∑ i, comp i).real univ = ∑ i, (comp i).real univ := by
    rw [measureReal_def, Measure.finsetSum_apply,
      ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rfl
  rw [htot]
  exact hL

end Submission.Obl.k4_fixed_budget_quadratic_recovery
