-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/EligibilityFormat.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates
import Submission.Obl.k4_eligibility_sign_description.Descriptions
import Submission.Obl.k4_dk4_smoothed_problem.BooleanFormat
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MvPolynomial Set
open Submission.Obl.k4_eligibility_sign_description

noncomputable section

/-- Two weak-sign tests determine the full three-valued sign. -/
def decodeSign (p n : Bool) : SignType := if p then if n then 0 else 1 else -1

theorem decodeSign_eval (u : ℝ) :
    decodeSign (decide (0 ≤ u)) (decide (0 ≤ -u)) = SignType.sign u := by
  rcases lt_trichotomy u 0 with hn | rfl | hp
  · simp [decodeSign, not_le_of_gt hn, sign_neg hn]
  · simp [decodeSign]
  · have hn : ¬ 0 ≤ -u := by linarith
    simp [decodeSign, hp.le, hn, sign_pos hp]

/-- A bounded sign description has a Boolean description with twice as many
polynomials, using each polynomial and its negative. -/
theorem signRep_boolFormat {σ X : Type*} (v : X → σ → ℝ) (m d : ℕ) (E : X → Prop)
    (h : SignRep v m d E) :
    Submission.Obl.k4_dk4_smoothed_problem.HasBoolPolynomialFormat v {x | E x} (m + m) d := by
  classical
  obtain ⟨p, B, hp, hB⟩ := h
  let q : Fin (m + m) → MvPolynomial σ ℝ := Fin.addCases p (fun i => -p i)
  let b : (Fin (m + m) → Bool) → Bool := fun w =>
    decide ((fun i => decodeSign (w (Fin.castAdd m i)) (w (Fin.natAdd m i))) ∈ B)
  refine ⟨q, ?_, b, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [q, Fin.addCases_left] using hp j
    · simpa only [q, Fin.addCases_right, totalDegree_neg] using hp j
  · intro x
    simpa only [mem_ofPred_eq, b, q, Fin.addCases_left, Fin.addCases_right,
      map_neg, decodeSign_eval, decide_eq_true_eq] using (hB x).symm

/-- Substitute coordinates in a sign representation without increasing degree. -/
theorem signRep_substitute {σ τ X Y : Type*} (v : X → σ → ℝ) (w : Y → τ → ℝ)
    (g : Y → X) (f : σ → MvPolynomial τ ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (hcoord : ∀ y i, MvPolynomial.eval (w y) (f i) = v (g y) i)
    (m d : ℕ) (E : X → Prop) (h : SignRep v m d E) :
    SignRep w m d (fun y => E (g y)) := by
  obtain ⟨p, B, hp, hB⟩ := h
  refine ⟨fun i => MvPolynomial.aeval f (p i), B,
    fun i => (degree_aeval_le _ _ hf).trans (hp i), ?_⟩
  intro y
  simpa only [eval_aeval_real, hcoord] using hB (g y)

/-- Boolean complements preserve all format bounds. -/
theorem fmt_compl {n D : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (h : fmt n H D S) : fmt n H D Sᶜ := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, p, hp, fun w => !(b w), ?_⟩
  intro x
  have hx := not_congr (hb x)
  cases hval : b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) <;> simp_all

/-- The format bound of a union is the sum of the two polynomial counts. -/
theorem fmt_union {n D D' : ℕ} {H H' : ℝ} {S T : Set (Fin n → ℝ)}
    (hS : fmt n H D S) (hT : fmt n H' D' T) :
    fmt n (H + H') (max D D') (S ∪ T) := by
  have hi := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
    (fmt_compl hS) (fmt_compl hT)
  simpa only [compl_inter, compl_compl] using fmt_compl hi

/-- Priority assignment subtracts earlier eligible sets at the same additive
format cost as an intersection. -/
theorem fmt_diff {n D D' : ℕ} {H H' : ℝ} {S T : Set (Fin n → ℝ)}
    (hS : fmt n H D S) (hT : fmt n H' D' T) :
    fmt n (H + H') (max D D') (S \ T) :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hS (fmt_compl hT)

/-- Slope/intercept coordinates used by the library's sign representations. -/
def coefficientLinePair (z : Fin 6 → ℝ) : E3 × E3 :=
  (WithLp.toLp 2 (fun i : Fin 3 => z (i.natAdd 3)),
    WithLp.toLp 2 (fun i : Fin 3 => z (i.castAdd 3)))

def coefficientSubstitution : Fin 3 ⊕ Fin 3 → MvPolynomial (Fin 6) ℝ :=
  Sum.elim (fun i => X (i.natAdd 3)) (fun i => X (i.castAdd 3))

theorem coefficientSubstitution_degree (i : Fin 3 ⊕ Fin 3) :
    (coefficientSubstitution i).totalDegree ≤ 1 := by
  rcases i with i | i <;> simp [coefficientSubstitution]

theorem coefficientSubstitution_eval (z : Fin 6 → ℝ) (i : Fin 3 ⊕ Fin 3) :
    MvPolynomial.eval z (coefficientSubstitution i) = coords (coefficientLinePair z) i := by
  rcases i with i | i <;> simp [coefficientSubstitution, coefficientLinePair, coords]

theorem coefficientLinePair_point (z : Fin 6 → ℝ) (t : ℝ) :
    ![t, ((coefficientLinePair z).2 + t • (coefficientLinePair z).1) 0,
      ((coefficientLinePair z).2 + t • (coefficientLinePair z).1) 1,
      ((coefficientLinePair z).2 + t • (coefficientLinePair z).1) 2] = x (0, z) t := by
  ext i
  fin_cases i <;> simp [x, coefficientLinePair, PiLp.add_apply, PiLp.smul_apply]

theorem raw_trace_abs_signRep (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (H l r : ℝ) (hlr : l ≤ r) :
    SignRep (fun z : Fin 6 → ℝ => z) 12 4 (fun z =>
      ∀ t ∈ Icc l r, |MvPolynomial.eval (x (0, z) t) R| ≤ H) := by
  have h := signRep_substitute coords (fun z : Fin 6 → ℝ => z) coefficientLinePair
    coefficientSubstitution coefficientSubstitution_degree coefficientSubstitution_eval
    12 4 _ (SignRep.trace_abs R hR H l r hlr)
  simpa only [coefficientLinePair_point] using h

theorem raw_derivative_large_signRep (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (H l r : ℝ) (hlr : l ≤ r) :
    SignRep (fun z : Fin 6 → ℝ => z) 12 4 (fun z =>
      ∃ t ∈ Icc l r, H ≤ |MvPolynomial.eval (x (0, z) t) (MvPolynomial.pderiv (3 : Fin 4) R)|) := by
  have h := signRep_substitute coords (fun z : Fin 6 → ℝ => z) coefficientLinePair
    coefficientSubstitution coefficientSubstitution_degree coefficientSubstitution_eval
    12 4 _ (SignRep.derivative_large R hR H l r hlr)
  simpa only [coefficientLinePair_point] using h

/-- Full line eligibility includes the three whole-block upper bounds and a
lower derivative witness somewhere in the block. -/
def eligibleCoefficients (R : MvPolynomial (Fin 4) ℝ) (H₀ H₁ H₂ b l r : ℝ)
    (z : Fin 6 → ℝ) : Prop :=
  (∀ t ∈ Icc l r, |MvPolynomial.eval (x (0, z) t) R| ≤ H₀) ∧
  (∀ t ∈ Icc l r, |MvPolynomial.eval (x (0, z) t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ H₁) ∧
  (∀ t ∈ Icc l r, |MvPolynomial.eval (x (0, z) t)
    (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ H₂) ∧
  ∃ t ∈ Icc l r, b ≤ |MvPolynomial.eval (x (0, z) t) (MvPolynomial.pderiv (3 : Fin 4) R)|

theorem eligibleCoefficients_format (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (H₀ H₁ H₂ b l r : ℝ) (hlr : l ≤ r) :
    fmt 6 96 4 {z | eligibleCoefficients R H₀ H₁ H₂ b l r z} := by
  have hD : (MvPolynomial.pderiv (3 : Fin 4) R).totalDegree ≤ 2 :=
    (degree_pderiv_le _ _).trans hR
  have hDD : (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R)).totalDegree ≤ 2 :=
    (degree_pderiv_le _ _).trans hD
  have hsign : SignRep (fun z : Fin 6 → ℝ => z) 48 4
      (eligibleCoefficients R H₀ H₁ H₂ b l r) := by
    have h := (raw_trace_abs_signRep R hR H₀ l r hlr).and
      ((raw_trace_abs_signRep _ hD H₁ l r hlr).and
        ((raw_trace_abs_signRep _ hDD H₂ l r hlr).and
          (raw_derivative_large_signRep R hR b l r hlr)))
    exact h.congr (fun _ => Iff.rfl)
  obtain ⟨p, hp, B, hB⟩ := signRep_boolFormat (fun z : Fin 6 → ℝ => z) 48 4
    (eligibleCoefficients R H₀ H₁ H₂ b l r) hsign
  exact ⟨96, le_rfl, p, hp, B, hB⟩

theorem fmt_empty (n D : ℕ) : fmt n 0 D (∅ : Set (Fin n → ℝ)) := by
  refine ⟨0, by norm_num, Fin.elim0, (fun i => Fin.elim0 i), (fun _ => false), ?_⟩
  intro x
  simp

/-- Finite unions have an additive polynomial-count bound. -/
theorem fmt_biUnion {n D : ℕ} {ι : Type*} (s : Finset ι)
    (H : ι → ℝ) (A : ι → Set (Fin n → ℝ))
    (hA : ∀ a ∈ s, fmt n (H a) D (A a)) :
    fmt n (∑ a ∈ s, H a) D (⋃ a ∈ s, A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fmt_empty n D
  | @insert a s ha ih =>
    have hS := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
    have hsets : (⋃ b ∈ insert a s, A b) = A a ∪ ⋃ b ∈ s, A b := by
      ext z
      simp only [mem_iUnion, Finset.mem_insert, mem_union]
      aesop
    rw [Finset.sum_insert ha, hsets]
    simpa only [max_self] using fmt_union (hA a (Finset.mem_insert_self _ _)) hS

/-- The maximal eligible trajectory set for one polynomial, inside an old assignment. -/
def eligibleTrajectories (A : Set Trajectory) (R : MvPolynomial (Fin 4) ℝ)
    (H₀ H₁ H₂ b l r : ℝ) : Set Trajectory :=
  {a | a ∈ A ∧ eligibleCoefficients R H₀ H₁ H₂ b l r a.2}

theorem eligibleTrajectories_measurable (A : Set Trajectory) (hAm : MeasurableSet A)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (H₀ H₁ H₂ b l r : ℝ) (hlr : l ≤ r) :
    MeasurableSet (eligibleTrajectories A R H₀ H₁ H₂ b l r) := by
  have hfmt := eligibleCoefficients_format R hR H₀ H₁ H₂ b l r hlr
  have hcoeff : MeasurableSet {z | eligibleCoefficients R H₀ H₁ H₂ b l r z} :=
    Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.measurableSet hfmt
  simpa only [eligibleTrajectories, Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage] using
    hAm.inter (hcoeff.preimage (measurable_snd : Measurable (Prod.snd : Trajectory → (Fin 6 → ℝ))))

theorem fmt_congr {n D : ℕ} {H : ℝ} {S T : Set (Fin n → ℝ)}
    (h : fmt n H D S) (hST : ∀ z, z ∈ S ↔ z ∈ T) : fmt n H D T := by
  obtain ⟨m, hm, p, hp, B, hB⟩ := h
  exact ⟨m, hm, p, hp, B, fun z => (hST z).symm.trans (hB z)⟩

theorem eligibleTrajectories_format (A : Set Trajectory) (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) (H₀ H₁ H₂ b l r H : ℝ) (D copy : ℕ) (hlr : l ≤ r)
    (hA : fmt 6 H D {z | (copy, z) ∈ A}) :
    fmt 6 (H + 96) (max D 4) {z | (copy, z) ∈ eligibleTrajectories A R H₀ H₁ H₂ b l r} := by
  have hi : fmt 6 (H + 96) (max D 4)
      ({z | (copy, z) ∈ A} ∩ {z | eligibleCoefficients R H₀ H₁ H₂ b l r z}) :=
    Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hA
      (eligibleCoefficients_format R hR H₀ H₁ H₂ b l r hlr)
  exact fmt_congr hi (fun _ => Iff.rfl)

/-- Maximal full-block eligibility for a concrete residual candidate. -/
def candidateEnvelope (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ)
    (ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (a : CandidateDatum C) : Set Trajectory :=
  eligibleTrajectories (A a.parent) a.test
    (Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev a.parent) + a.gain * L))
    (Nk ^ (ρ * gain * L + ε) * B (γ a.parent))
    (Nk ^ (ρ * gain * L + ε) * B (γ a.parent) ^ 2 / δ Nk (r (lev a.parent) + a.gain * L))
    (B (γ a.parent) / Nk ^ (ρ * gain * L + ε))
    ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
    (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent))

/-- Every original counted incidence lies on a maximally eligible trajectory. -/
theorem counted_subset_candidateEnvelope
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → MeasureTheory.Measure Trajectory)
    (B : Fin W → ℝ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (a : CandidateDatum C)
    (hg : CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a)
    (hc : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a) :
    ∀ p ∈ a.counted, p.1 ∈ candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a := by
  intro p hp
  obtain ⟨_, _, _, _, _, _, hAsub, hupper⟩ := hg
  obtain ⟨hline, htime, hlower⟩ := hc.2.2.1 p hp
  refine ⟨hAsub hline, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hupper p.1 hline t ht).1
  · intro t ht
    exact (hupper p.1 hline t ht).2.1
  · intro t ht
    exact (hupper p.1 hline t ht).2.2
  · exact ⟨p.2, htime, hlower⟩

theorem candidateEnvelope_format
    (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (a : CandidateDatum C)
    (hR : a.test.totalDegree ≤ 2) (H : ℝ) (D copy : ℕ)
    (hA : fmt 6 H D {z | (copy, z) ∈ A a.parent}) :
    fmt 6 (H + 96) (max D 4)
      {z | (copy, z) ∈ candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a} := by
  apply eligibleTrajectories_format
  · exact hR
  · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · exact hA

theorem candidateEnvelope_measurable
    (Nk L : ℝ) (W C : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (a : CandidateDatum C)
    (hR : a.test.totalDegree ≤ 2) (hA : MeasurableSet (A a.parent)) :
    MeasurableSet (candidateEnvelope Nk L W C B ρ gain ε r T lev γ j A a) := by
  apply eligibleTrajectories_measurable
  · exact hA
  · exact hR
  · exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end

end Submission.Obl.k4_quadratic_finite_greedy_cover
