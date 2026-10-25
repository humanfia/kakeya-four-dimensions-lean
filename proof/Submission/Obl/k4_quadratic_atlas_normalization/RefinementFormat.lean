import Submission.Obl.k4_quadratic_atlas_normalization.Endpoints
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MvPolynomial MeasureTheory

noncomputable section

private abbrev BF {n : ℕ} (H : ℝ) (D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D S

/-- A constant-false lookup uses no polynomial tests. -/
theorem fmt_empty (n D : ℕ) {H : ℝ} (hH : 0 ≤ H) : fmt n H D ∅ := by
  refine ⟨0, by simpa using hH, Fin.elim0, fun i => i.elim0, fun _ => false, ?_⟩
  intro z
  simp

lemma format_compl {n D : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (hS : BF H D S) : BF H D Sᶜ := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := hS
  refine ⟨m, hm, p, hp, fun v => !(b v), ?_⟩
  intro z
  simpa using not_congr (hb z)

lemma format_union {n D D' : ℕ} {H H' : ℝ} {S T : Set (Fin n → ℝ)}
    (hS : BF H D S) (hT : BF H' D' T) : BF (H + H') (max D D') (S ∪ T) := by
  have h := format_compl (hS := (format_compl hS).inter (format_compl hT))
  simpa only [Set.compl_inter, compl_compl] using h

lemma format_abs_le {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (H : ℝ) :
    BF 2 d {z | |eval z P| ≤ H} := by
  classical
  refine ⟨2, le_rfl, ![C H - P, C H + P], ?_, fun b => b 0 && b 1, ?_⟩
  · intro i
    fin_cases i
    · exact (totalDegree_sub _ _).trans (by simpa using hP)
    · exact (totalDegree_add _ _).trans (by simpa using hP)
  · intro z
    simp only [Set.mem_ofPred_eq, Bool.and_eq_true, Matrix.cons_val_zero,
      Matrix.cons_val_one, decide_eq_true_eq, map_sub, map_add, eval_C]
    constructor
    · intro h
      obtain ⟨hl, hu⟩ := abs_le.mp h
      constructor <;> linarith
    · rintro ⟨hl, hu⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma format_abs_ge {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (H : ℝ) :
    BF 2 d {z | H ≤ |eval z P|} := by
  classical
  refine ⟨2, le_rfl, ![P - C H, -P - C H], ?_, fun b => b 0 || b 1, ?_⟩
  · intro i
    fin_cases i
    · exact (totalDegree_sub _ _).trans (by simpa using hP)
    · exact (totalDegree_sub _ _).trans (by simpa using hP)
  · intro z
    simp only [Set.mem_ofPred_eq, Bool.or_eq_true, Matrix.cons_val_zero,
      Matrix.cons_val_one, decide_eq_true_eq, map_sub, map_neg, eval_C]
    rw [le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)

/-- Endpoint bin predicates have a fixed eight-test description. -/
theorem format_max_abs_bin {n d : ℕ} (P Q : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d) (lo hi : ℝ) :
    BF 8 d {z | lo ≤ max |eval z P| |eval z Q| ∧ max |eval z P| |eval z Q| ≤ hi} := by
  have hl := format_union (format_abs_ge P hP lo) (format_abs_ge Q hQ lo)
  have hu := (format_abs_le P hP hi).inter (format_abs_le Q hQ hi)
  have h := hl.inter hu
  convert h using 1 <;> try norm_num
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union ]

/-- Substitutions of degree at most `d` multiply total degree by at most `d`. -/
theorem degree_aeval_le_mul {σ τ : Type*} (P : MvPolynomial σ ℝ)
    (f : σ → MvPolynomial τ ℝ) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d) :
    (aeval f P).totalDegree ≤ d * P.totalDegree := by
  classical
  rw [aeval_def, MvPolynomial.eval₂]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e he
  change (C (P.coeff e) * ∏ i ∈ e.support, f i ^ e i).totalDegree ≤ d * P.totalDegree
  apply (Submission.Obl.k4_eligibility_sign_description.degree_C_mul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i ∈ e.support, d * e i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by nlinarith [hf i])
    _ = d * (∑ i ∈ e.support, e i) := by rw [Finset.mul_sum]
    _ ≤ d * P.totalDegree := Nat.mul_le_mul_left d (le_totalDegree he)

noncomputable def fixedSub (t : ℝ) : Fin 4 → MvPolynomial (Fin 6) ℝ :=
  ![C t, X 0 + C t * X 3, X 1 + C t * X 4, X 2 + C t * X 5]

noncomputable def fixedTrace (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    MvPolynomial (Fin 6) ℝ := aeval (fixedSub t) R

lemma fixedTrace_degree (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (fixedTrace R t).totalDegree ≤ R.totalDegree := by
  apply Submission.Obl.k4_eligibility_sign_description.degree_aeval_le
  intro i
  fin_cases i
  · simp [fixedSub]
  all_goals
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply (totalDegree_mul _ _).trans
      simp

lemma eval_fixedTrace (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) (i : ℕ) (z : Fin 6 → ℝ) :
    eval z (fixedTrace R t) = eval (x (i, z) t) R := by
  rw [fixedTrace, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
  apply congrArg (fun w : Fin 4 → ℝ => eval w R)
  funext j
  fin_cases j <;> simp [fixedSub, x]

noncomputable def incidentSub : Fin 4 → MvPolynomial (Fin 7) ℝ :=
  ![X 6, X 0 + X 6 * X 3, X 1 + X 6 * X 4, X 2 + X 6 * X 5]

noncomputable def incidentTrace (R : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 7) ℝ := aeval incidentSub R

lemma incidentTrace_degree (R : MvPolynomial (Fin 4) ℝ) :
    (incidentTrace R).totalDegree ≤ 2 * R.totalDegree := by
  apply degree_aeval_le_mul
  intro i
  fin_cases i
  · simp [incidentSub]
  all_goals
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply (totalDegree_mul _ _).trans
      simp

lemma eval_incidentTrace (R : MvPolynomial (Fin 4) ℝ) (i : ℕ) (z : Fin 7 → ℝ) :
    eval z (incidentTrace R) = eval (x (i, fun e : Fin 6 => z e.castSucc) (z 6)) R := by
  rw [incidentTrace, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
  apply congrArg (fun w : Fin 4 → ℝ => eval w R)
  funext j
  fin_cases j <;> simp [incidentSub, x]

/-- A fixed derivative-size bin in line space. -/
def binRegion (R : MvPolynomial (Fin 4) ℝ) (s e lo hi : ℝ) : Set Line :=
  {l | lo ≤ derivativeMax R s e l ∧ derivativeMax R s e l ≤ hi}

/-- The derivative floor imposed on selected incidences. -/
def derivativeFloorSet (R : MvPolynomial (Fin 4) ℝ) (H : ℝ) : Set Incidence :=
  {p | H ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) R)|}

lemma continuous_line_eval (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    Continuous (fun l : Line => eval (x l t) R) := by
  apply (continuous_eval R).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [x] <;> fun_prop

lemma continuous_incident_eval (R : MvPolynomial (Fin 4) ℝ) :
    Continuous (fun p : Incidence => eval (x p.1 p.2) R) := by
  apply (continuous_eval R).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [x] <;> fun_prop

lemma measurableSet_binRegion (R : MvPolynomial (Fin 4) ℝ) (s e lo hi : ℝ) :
    MeasurableSet (binRegion R s e lo hi) := by
  have hc : Continuous (derivativeMax R s e) :=
    (continuous_line_eval (pderiv 3 R) s).abs.max (continuous_line_eval (pderiv 3 R) e).abs
  exact (measurableSet_le measurable_const hc.measurable).inter
    (measurableSet_le hc.measurable measurable_const)

lemma measurableSet_derivativeFloorSet (R : MvPolynomial (Fin 4) ℝ) (H : ℝ) :
    MeasurableSet (derivativeFloorSet R H) :=
  measurableSet_le measurable_const (continuous_incident_eval (pderiv 3 R)).abs.measurable

lemma format_binRegion (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (s e lo hi : ℝ) (i : ℕ) :
    fmt 6 8 1 {z | (i, z) ∈ binRegion R s e lo hi} := by
  have hd : (pderiv (3 : Fin 4) R).totalDegree ≤ 1 :=
    Submission.Obl.k4_quadratic_selector_sweep.totalDegree_pderiv_le R 3 hR
  have h := format_max_abs_bin (fixedTrace (pderiv 3 R) s) (fixedTrace (pderiv 3 R) e)
    ((fixedTrace_degree _ _).trans hd) ((fixedTrace_degree _ _).trans hd) lo hi
  change BF 8 1 _
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, binRegion, derivativeMax]
  rw [eval_fixedTrace _ s i z, eval_fixedTrace _ e i z]

lemma format_incident_binRegion (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (s e lo hi : ℝ) (i : ℕ) :
    fmt 7 8 1 {z : Fin 7 → ℝ |
      (i, fun j : Fin 6 => z j.castSucc) ∈ binRegion R s e lo hi} := by
  have h : BF 8 1 {z | (i, z) ∈ binRegion R s e lo hi} :=
    format_binRegion R hR s e lo hi i
  have hp := h.affine_preimage (fun j : Fin 6 => (X j.castSucc : MvPolynomial (Fin 7) ℝ))
    (by intro j; simp)
  change BF 8 1 _
  simpa only [Set.preimage, Set.mem_ofPred_eq, eval_X] using hp

lemma format_derivativeFloorSet (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) (H : ℝ) (i : ℕ) :
    fmt 7 2 2 {z : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ derivativeFloorSet R H} := by
  have hd : (pderiv (3 : Fin 4) R).totalDegree ≤ 1 :=
    Submission.Obl.k4_quadratic_selector_sweep.totalDegree_pderiv_le R 3 hR
  have hd' : (incidentTrace (pderiv 3 R)).totalDegree ≤ 2 :=
    (incidentTrace_degree _).trans (by omega)
  have h := format_abs_ge (incidentTrace (pderiv 3 R)) hd' H
  change BF 2 2 _
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, derivativeFloorSet]
  rw [eval_incidentTrace _ i z]

/-- Refinement of assignments adds only eight affine tests. -/
theorem format_bin_assignment (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (s e lo hi H : ℝ) (D : ℕ) (A : Set Line)
    (hA : ∀ i, fmt 6 H D {z | (i, z) ∈ A}) (i : ℕ) :
    fmt 6 (H + 8) (max D 1) {z | (i, z) ∈ A ∩ binRegion R s e lo hi} := by
  exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
    (hA i) (format_binRegion R hR s e lo hi i)

/-- Refinement and derivative deletion add ten tests, of degree at most two. -/
theorem format_bin_selection (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (s e lo hi floor H : ℝ) (D : ℕ) (F : Set Incidence)
    (hF : ∀ i, fmt 7 H D {z : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ F}) (i : ℕ) :
    fmt 7 (H + 10) (max D 2) {z : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈
        F ∩ (Prod.fst ⁻¹' binRegion R s e lo hi ∩ derivativeFloorSet R floor)} := by
  have hb : BF 8 1 {z : Fin 7 → ℝ |
      (i, fun j : Fin 6 => z j.castSucc) ∈ binRegion R s e lo hi} :=
    format_incident_binRegion R hR s e lo hi i
  have hf : BF 2 2 {z : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ derivativeFloorSet R floor} :=
    format_derivativeFloorSet R hR floor i
  have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter (hF i) (hb.inter hf)
  change BF (H + 10) (max D 2) _
  convert h using 1 <;> try norm_num
  rfl

end
end Submission.Obl.k4_quadratic_atlas_normalization
