import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatRule
import Submission.Obl.k4_coarsened_outer_horizon_composition.CrossingsFormat

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set MvPolynomial

/-- The list of compatible envelopes in one original world. -/
noncomputable def envelopeList {C W : ℕ} (γ : Fin C → Fin W) (S : Fin C → Set Obs)
    (w : Fin W) (o : Obs) : Finset (Fin C) := by
  classical
  exact Finset.univ.filter (fun i => γ i = w ∧ o ∈ S i)

/-- A cardinality cutoff is one Boolean decision on the fixed-bin crossing
predicates, so its number of tests is linear in the number of envelopes. -/
theorem fmt_envelope_count {C W D : ℕ} (γ : Fin C → Fin W) (S : Fin C → Set Obs)
    (H : ℝ) (hS : ∀ i (j : ℤ), fmt 3 H D {z : Fin 3 → ℝ | (WithLp.toLp 2 z, j) ∈ S i})
    (w : Fin W) (j : ℤ) (θ : ℝ) :
    fmt 3 ((C : ℝ) * H) D {z : Fin 3 → ℝ |
      ((envelopeList γ S w (WithLp.toLp 2 z, j)).card : ℝ) ≤ θ} := by
  classical
  have h := fmt_rule_uniform (fun i => {z : Fin 3 → ℝ | (WithLp.toLp 2 z, j) ∈ S i}) H
    (fun i => hS i j)
    (fun pred : Fin C → Prop => ((Finset.univ.filter (fun i => γ i = w ∧ pred i)).card : ℝ) ≤ θ)
  simpa only [Fintype.card_fin, envelopeList, mem_ofPred_eq] using h

noncomputable def incidentBasePolynomials : Fin 3 → MvPolynomial (Fin 7) ℝ :=
  ![X 6, X 0 + X 6 * X 3, X 1 + X 6 * X 4]

lemma incidentBasePolynomials_degree (i : Fin 3) :
    (incidentBasePolynomials i).totalDegree ≤ 2 := by
  fin_cases i
  · simp [incidentBasePolynomials]
  all_goals
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

noncomputable def incidentObs (B a : ℝ) (z : Fin 7 → ℝ) : Obs :=
  obs B a ((0, fun i => z i.castSucc), z 6)

lemma incidentBasePolynomials_eval (z : Fin 7 → ℝ) :
    (fun i => eval z (incidentBasePolynomials i)) = (incidentObs 0 1 z).1.ofLp := by
  funext i
  fin_cases i <;> simp [incidentBasePolynomials, incidentObs, obs, x]

noncomputable def incidentHiddenPolynomial (B a : ℝ) : MvPolynomial (Fin 7) ℝ :=
  C (B / a) * (X 2 + X 6 * X 5)

lemma incidentHiddenPolynomial_degree (B a : ℝ) :
    (incidentHiddenPolynomial B a).totalDegree ≤ 2 := by
  apply (Submission.Obl.k4_eligibility_sign_description.degree_C_mul_le _ _).trans
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

lemma incidentHiddenPolynomial_eval (B a : ℝ) (z : Fin 7 → ℝ) :
    ⌊eval z (incidentHiddenPolynomial B a)⌋ = (incidentObs B a z).2 := by
  congr 1
  simp [incidentHiddenPolynomial, incidentObs, obs, x, Matrix.vecHead, Matrix.vecTail]
  ring

/-- Arbitrary fixed-bin polynomial observation predicates pull back to native
incidence coordinates with a polynomial test budget. -/
theorem fmt_native_observation_cut {D : ℕ} (S : Set Obs) (H : ℝ)
    (hS : ∀ j : ℤ, fmt 3 H D {z : Fin 3 → ℝ | (WithLp.toLp 2 z, j) ∈ S})
    (bins : Finset ℤ) (B a : ℝ) :
    fmt 7 ((bins.card : ℝ) * (2 + H)) (max 2 (2 * D))
      {z : Fin 7 → ℝ | (incidentObs B a z).2 ∈ bins ∧ incidentObs B a z ∈ S} := by
  classical
  let F : bins → Set (Fin 7 → ℝ) := fun j =>
    {z | (incidentObs B a z).2 = j.val} ∩
      {z | ((incidentObs B a z).1, j.val) ∈ S}
  have hF (j : bins) : fmt 7 (2 + H) (max 2 (2 * D)) (F j) := by
    have hfloor := fmt_floor_eq (incidentHiddenPolynomial B a) (incidentHiddenPolynomial_degree B a) j.val
    have hbase := fmt_polynomial_preimage (hS j.val) incidentBasePolynomials incidentBasePolynomials_degree
    have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hfloor hbase
    have heq : F j = {z : Fin 7 → ℝ | ⌊eval z (incidentHiddenPolynomial B a)⌋ = j.val} ∩
        ((fun z i => eval z (incidentBasePolynomials i)) ⁻¹'
          {z : Fin 3 → ℝ | (WithLp.toLp 2 z, j.val) ∈ S}) := by
      ext z
      simp only [F, mem_inter_iff, mem_ofPred_eq, mem_preimage, incidentHiddenPolynomial_eval,
        incidentBasePolynomials_eval]
      rfl
    rw [heq]
    exact h
  have h := fmt_rule_uniform F (2 + H) hF (fun pred : bins → Prop => ∃ j, pred j)
  have heq : {z : Fin 7 → ℝ | (incidentObs B a z).2 ∈ bins ∧ incidentObs B a z ∈ S} =
      {z : Fin 7 → ℝ | ∃ j : bins, z ∈ F j} := by
    ext z
    constructor
    · rintro ⟨hz, hS⟩
      exact ⟨⟨(incidentObs B a z).2, hz⟩, rfl, hS⟩
    · rintro ⟨j, hj, hS⟩
      change (incidentObs B a z).2 = j.val at hj
      change ((incidentObs B a z).1, j.val) ∈ S at hS
      refine ⟨hj.symm ▸ j.property, ?_⟩
      simpa only [← hj, Prod.eta] using hS
  rw [heq]
  simpa only [Fintype.card_coe] using h

/-- Specialization of the native cutoff format to an envelope-list cardinality
bound. The fixed-bin hypotheses are supplied by `format_crossing_bin`. -/
theorem fmt_native_envelope_cut {C W D : ℕ} (γ : Fin C → Fin W) (S : Fin C → Set Obs)
    (H : ℝ) (hS : ∀ i (j : ℤ), fmt 3 H D {z : Fin 3 → ℝ | (WithLp.toLp 2 z, j) ∈ S i})
    (w : Fin W) (θ : ℝ) (bins : Finset ℤ) (B a : ℝ) :
    fmt 7 ((bins.card : ℝ) * (2 + (C : ℝ) * H)) (max 2 (2 * D))
      {z : Fin 7 → ℝ | (incidentObs B a z).2 ∈ bins ∧
        ((envelopeList γ S w (incidentObs B a z)).card : ℝ) ≤ θ} :=
  fmt_native_observation_cut {o | ((envelopeList γ S w o).card : ℝ) ≤ θ}
    ((C : ℝ) * H) (fun j => fmt_envelope_count γ S H hS w j θ) bins B a

end Submission.Obl.k4_coarsened_outer_horizon_composition
