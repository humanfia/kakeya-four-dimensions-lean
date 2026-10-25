import Mathlib

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_dyadic_reduction

noncomputable section

/-- The multiplicative oscillatory integral used in the reduction. -/
def phase {n : ℕ} (ξ : ℝ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * ξ * (∏ j, x j) : ℝ) : ℂ) * Complex.I)

lemma continuous_phase {n : ℕ} (ξ : ℝ) : Continuous (phase (n := n) ξ) := by
  unfold phase
  fun_prop

lemma norm_phase {n : ℕ} (ξ : ℝ) (x : Fin n → ℝ) : ‖phase ξ x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

lemma integrable_phase {n : ℕ} (ξ : ℝ) (ν : Measure (Fin n → ℝ))
    [IsFiniteMeasure ν] : Integrable (phase ξ) ν := by
  exact Integrable.of_bound (continuous_phase ξ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (norm_phase ξ x).le)

lemma norm_integral_phase_le {n : ℕ} (ξ : ℝ) (ν : Measure (Fin n → ℝ))
    [IsFiniteMeasure ν] : ‖∫ x, phase ξ x ∂ν‖ ≤ ν.real univ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (C := (1 : ℝ)) (Filter.Eventually.of_forall fun x => (norm_phase ξ x).le)

/-- Finite products distribute over finite sums of finite measures. -/
lemma pi_finsetSum {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (ν : ι → κ → Measure ℝ) [∀ i k, IsFiniteMeasure (ν i k)] :
    Measure.pi (fun i => ∑ k, ν i k) =
      ∑ p : ι → κ, Measure.pi (fun i => ν i (p i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply, Measure.pi_pi]
  exact (Fintype.prod_sum fun i k => ν i k (s i)).symm

/-- Scalars can be taken outside a finite product measure. -/
lemma pi_smul {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  classical
  haveI (i : ι) : IsFiniteMeasure (c i • ν i) :=
    ⟨by simpa [Measure.smul_apply, smul_eq_mul] using
      ENNReal.mul_lt_top (hc i).lt_top (measure_lt_top (ν i) univ)⟩
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

lemma phase_mul {n : ℕ} (a : Fin n → ℝ) (ξ : ℝ) (x : Fin n → ℝ) :
    phase ξ (fun j => a j * x j) = phase (ξ * ∏ j, a j) x := by
  simp only [phase, Finset.prod_mul_distrib]
  congr 3
  push_cast
  ring

/-- Discarding a set of one-dimensional mass `b` costs at most `n*b`. -/
lemma norm_integral_pi_cut_le {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (G : Set ℝ) (hG : MeasurableSet G) (ξ : ℝ) :
    ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => μ)‖ ≤
      ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => μ.restrict G)‖ +
        n * μ.real Gᶜ := by
  classical
  let P : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ)
  let Q : Set (Fin n → ℝ) := Set.univ.pi (fun _ => G)
  have hQ : MeasurableSet Q := MeasurableSet.univ_pi (fun _ => hG)
  have hcomp : Qᶜ = ⋃ j : Fin n, (Function.eval j) ⁻¹' Gᶜ := by
    ext x
    simp [Q, Set.mem_pi, not_forall]
  have hbad : P.real Qᶜ ≤ n * μ.real Gᶜ := by
    rw [hcomp]
    calc
      P.real (⋃ j : Fin n, (Function.eval j) ⁻¹' Gᶜ) ≤
          ∑ j : Fin n, P.real ((Function.eval j) ⁻¹' Gᶜ) :=
        measureReal_iUnion_fintype_le _
      _ = n * μ.real Gᶜ := by
        have hpre (j : Fin n) : P.real ((Function.eval j) ⁻¹' Gᶜ) = μ.real Gᶜ :=
          (measurePreserving_eval (fun _ : Fin n => μ) j).measureReal_preimage
            hG.compl.nullMeasurableSet
        simp only [hpre, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit := integral_add_compl hQ (integrable_phase ξ P)
  rw [← hsplit]
  calc
    ‖(∫ x in Q, phase ξ x ∂P) + ∫ x in Qᶜ, phase ξ x ∂P‖ ≤
        ‖∫ x in Q, phase ξ x ∂P‖ + ‖∫ x in Qᶜ, phase ξ x ∂P‖ := norm_add_le _ _
    _ ≤ ‖∫ x in Q, phase ξ x ∂P‖ + P.real Qᶜ := by
      gcongr
      simpa using norm_integral_phase_le ξ (P.restrict Qᶜ)
    _ ≤ _ := by
      rw [show P.restrict Q = Measure.pi (fun _ : Fin n => μ.restrict G) from
        Measure.restrict_pi_pi _ _]
      exact add_le_add le_rfl hbad

/-- A weighted estimate on each box sums without a loss in the number of boxes. -/
lemma norm_integral_pi_sum_le {n : ℕ} {κ : Type*} [Fintype κ]
    (ν : κ → Measure ℝ) [∀ k, IsFiniteMeasure (ν k)]
    (hmass : ∑ k, (ν k).real univ ≤ 1) {A : ℝ} (hA : 0 ≤ A) (ξ : ℝ)
    (hbox : ∀ p : Fin n → κ,
      ‖∫ x, phase ξ x ∂Measure.pi (fun j => ν (p j))‖ ≤
        A * ∏ j, (ν (p j)).real univ) :
    ‖∫ x, phase ξ x ∂Measure.pi (fun _ : Fin n => ∑ k, ν k)‖ ≤ A := by
  classical
  rw [pi_finsetSum (fun (_ : Fin n) k => ν k), integral_finsetSum_measure]
  · calc
      ‖∑ p : Fin n → κ, ∫ x, phase ξ x ∂Measure.pi (fun j => ν (p j))‖ ≤
          ∑ p : Fin n → κ, ‖∫ x, phase ξ x ∂Measure.pi (fun j => ν (p j))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p : Fin n → κ, A * ∏ j, (ν (p j)).real univ :=
        Finset.sum_le_sum fun p _ => hbox p
      _ = A * (∑ k, (ν k).real univ) ^ n := by
        rw [← Finset.mul_sum, Fintype.sum_pow]
      _ ≤ A * 1 := by
        gcongr
        exact pow_le_one₀ (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) hmass
      _ = A := mul_one _
  · intro p _
    exact integrable_phase _ _

end
end Submission.Obl.k4_oss_dyadic_reduction
