/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/Fmt.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Submission.Obl.k4_horizon_asymptotic_assembly.Defs

/-!
# Boolean polynomial format calculus for `Outer.Fmt`
-/

open MeasureTheory MvPolynomial

namespace Submission.Obl.k4_horizon_asymptotic_assembly.Outer

theorem Fmt.mono {n : ℕ} {H H' : ℝ} {D D' : ℕ} {A : Set (Fin n → ℝ)} (h : Fmt n H D A)
    (hH : H ≤ H') (hD : D ≤ D') : Fmt n H' D' A := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  exact ⟨m, hm.trans hH, p, fun i => (hp i).trans hD, b, hb⟩

theorem Fmt.of_eq {n : ℕ} {H : ℝ} {D : ℕ} {A A' : Set (Fin n → ℝ)} (h : Fmt n H D A)
    (hA : A = A') : Fmt n H D A' := by
  subst hA
  exact h

theorem Fmt.empty (n : ℕ) {H : ℝ} (hH : 0 ≤ H) (D : ℕ) : Fmt n H D ∅ := by
  refine ⟨0, by simpa using hH, fun i => i.elim0, fun i => i.elim0, fun _ => false, ?_⟩
  intro x
  simp

theorem Fmt.univ (n : ℕ) {H : ℝ} (hH : 0 ≤ H) (D : ℕ) : Fmt n H D Set.univ := by
  refine ⟨0, by simpa using hH, fun i => i.elim0, fun i => i.elim0, fun _ => true, ?_⟩
  intro x
  simp

theorem Fmt.nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D) :
    Fmt n 1 D {x | 0 ≤ eval x p} := by
  refine ⟨1, by simp, fun _ => p, fun _ => hp, fun v => v 0, ?_⟩
  intro x
  simp

theorem Fmt.compl {n : ℕ} {H : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : Fmt n H D A) :
    Fmt n H D Aᶜ := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, p, hp, fun v => !b v, ?_⟩
  intro x
  rw [Set.mem_compl_iff, hb x]
  simp

theorem Fmt.inter {n : ℕ} {H₁ H₂ : ℝ} {D : ℕ} {A B : Set (Fin n → ℝ)} (h₁ : Fmt n H₁ D A)
    (h₂ : Fmt n H₂ D B) : Fmt n (H₁ + H₂) D (A ∩ B) := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h₁
  obtain ⟨m', hm', p', hp', b', hb'⟩ := h₂
  refine ⟨m + m', by push_cast; exact add_le_add hm hm', Fin.addCases p p', ?_,
    fun v => b (fun i => v (Fin.castAdd m' i)) && b' (fun i => v (Fin.natAdd m i)), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hp j
    · simpa only [Fin.addCases_right] using hp' j
  · intro x
    simp only [Set.mem_inter_iff, Bool.and_eq_true, Fin.addCases_left, Fin.addCases_right]
    exact and_congr (hb x) (hb' x)

theorem Fmt.union {n : ℕ} {H₁ H₂ : ℝ} {D : ℕ} {A B : Set (Fin n → ℝ)} (h₁ : Fmt n H₁ D A)
    (h₂ : Fmt n H₂ D B) : Fmt n (H₁ + H₂) D (A ∪ B) := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h₁
  obtain ⟨m', hm', p', hp', b', hb'⟩ := h₂
  refine ⟨m + m', by push_cast; exact add_le_add hm hm', Fin.addCases p p', ?_,
    fun v => b (fun i => v (Fin.castAdd m' i)) || b' (fun i => v (Fin.natAdd m i)), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hp j
    · simpa only [Fin.addCases_right] using hp' j
  · intro x
    simp only [Set.mem_union, Bool.or_eq_true, Fin.addCases_left, Fin.addCases_right]
    exact or_congr (hb x) (hb' x)

theorem Fmt.diff {n : ℕ} {H₁ H₂ : ℝ} {D : ℕ} {A B : Set (Fin n → ℝ)} (h₁ : Fmt n H₁ D A)
    (h₂ : Fmt n H₂ D B) : Fmt n (H₁ + H₂) D (A \ B) :=
  (h₁.inter h₂.compl).of_eq (Set.sdiff_eq A B).symm

/-- Finite intersections; the counts add up. -/
theorem Fmt.iInter {n m : ℕ} {H : ℝ} {D : ℕ} (hH : 0 ≤ H) (A : Fin m → Set (Fin n → ℝ))
    (h : ∀ i, Fmt n H D (A i)) : Fmt n (m * H) D (⋂ i, A i) := by
  induction m with
  | zero =>
    exact (Fmt.univ n (mul_nonneg (Nat.cast_nonneg _) hH) D).of_eq (Set.iInter_of_empty A).symm
  | succ m ih =>
    have h' := (h 0).inter (ih (fun i => A i.succ) (fun i => h i.succ))
    refine (h'.mono (le_of_eq (by push_cast; ring)) le_rfl).of_eq ?_
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact (Fin.forall_fin_succ (P := fun i => x ∈ A i)).symm

/-- Finite unions; the counts add up. -/
theorem Fmt.iUnion {n m : ℕ} {H : ℝ} {D : ℕ} (hH : 0 ≤ H) (A : Fin m → Set (Fin n → ℝ))
    (h : ∀ i, Fmt n H D (A i)) : Fmt n (m * H) D (⋃ i, A i) := by
  induction m with
  | zero =>
    exact (Fmt.empty n (mul_nonneg (Nat.cast_nonneg _) hH) D).of_eq (Set.iUnion_of_empty A).symm
  | succ m ih =>
    have h' := (h 0).union (ih (fun i => A i.succ) (fun i => h i.succ))
    refine (h'.mono (le_of_eq (by push_cast; ring)) le_rfl).of_eq ?_
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    exact (Fin.exists_fin_succ (P := fun i => x ∈ A i)).symm

theorem Fmt.le_const {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c : ℝ) : Fmt n 1 D {x | eval x p ≤ c} := by
  have hdeg : (C c - p).totalDegree ≤ D := by
    refine (totalDegree_sub _ _).trans (max_le ?_ hp)
    rw [totalDegree_C]
    exact Nat.zero_le _
  refine (Fmt.nonneg (C c - p) hdeg).of_eq ?_
  ext x
  simp [sub_nonneg]

theorem Fmt.const_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c : ℝ) : Fmt n 1 D {x | c ≤ eval x p} := by
  have hdeg : (p - C c).totalDegree ≤ D := (totalDegree_sub_C_le p c).trans hp
  refine (Fmt.nonneg (p - C c) hdeg).of_eq ?_
  ext x
  simp [sub_nonneg]

theorem Fmt.lt_const {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c : ℝ) : Fmt n 1 D {x | eval x p < c} := by
  refine (Fmt.const_le p hp c).compl.of_eq ?_
  ext x
  simp

theorem Fmt.const_lt {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c : ℝ) : Fmt n 1 D {x | c < eval x p} := by
  refine (Fmt.le_const p hp c).compl.of_eq ?_
  ext x
  simp

theorem Fmt.abs_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c : ℝ) : Fmt n 2 D {x | |eval x p| ≤ c} := by
  refine (((Fmt.const_le p hp (-c)).inter (Fmt.le_const p hp c)).mono
    (by norm_num) le_rfl).of_eq ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact (_root_.abs_le).symm

/-- Interval condition `c ≤ p < c'` (half-open bins). -/
theorem Fmt.Ico {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {D : ℕ} (hp : p.totalDegree ≤ D)
    (c c' : ℝ) : Fmt n 2 D {x | c ≤ eval x p ∧ eval x p < c'} := by
  refine (((Fmt.const_le p hp c).inter (Fmt.lt_const p hp c')).mono
    (by norm_num) le_rfl).of_eq ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]

private theorem totalDegree_C_mul_le' {m : ℕ} (a : ℝ) (q : MvPolynomial (Fin m) ℝ) :
    (C a * q).totalDegree ≤ q.totalDegree := by
  simpa using totalDegree_mul (C a) q

/-- Total degree of a substitution. -/
theorem totalDegree_aeval_le {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (f : Fin n → MvPolynomial (Fin m) ℝ) {e : ℕ} (hf : ∀ i, (f i).totalDegree ≤ e) :
    (aeval f p).totalDegree ≤ p.totalDegree * e := by
  classical
  rw [aeval_def, eval₂]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  change (C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree * e
  apply (totalDegree_C_mul_le' _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i * e := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (d i) (hf i))
    _ = (∑ i ∈ d.support, d i) * e := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * e := Nat.mul_le_mul_right e (le_totalDegree hd)

theorem eval_aeval_eq {n m : ℕ} (p : MvPolynomial (Fin n) ℝ) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (x : Fin m → ℝ) : eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
  simpa only [aeval_def, algebraMap_eq, Function.comp_def] using (eval_assoc f x p).symm

/-- Preimage under a polynomial map. -/
theorem Fmt.preimage {n m : ℕ} {H : ℝ} {D e : ℕ} {A : Set (Fin n → ℝ)} (h : Fmt n H D A)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ e) :
    Fmt m H (D * e) ((fun x i => eval x (f i)) ⁻¹' A) := by
  obtain ⟨r, hr, p, hp, b, hb⟩ := h
  refine ⟨r, hr, fun i => aeval f (p i), ?_, b, ?_⟩
  · exact fun i => (totalDegree_aeval_le (p i) f hf).trans (Nat.mul_le_mul_right e (hp i))
  · intro x
    simpa only [Set.mem_preimage, eval_aeval_eq] using hb (fun i => eval x (f i))

theorem Fmt.measurableSet {n : ℕ} {H : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : Fmt n H D A) :
    MeasurableSet A := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  have hcoord (i : Fin m) : Measurable (fun x : Fin n → ℝ => decide (0 ≤ eval x (p i))) := by
    have hs : MeasurableSet {x : Fin n → ℝ | 0 ≤ eval x (p i)} :=
      measurableSet_le measurable_const (continuous_eval (p i)).measurable
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hs
  have hmeas : Measurable (fun x : Fin n → ℝ => b (fun i => decide (0 ≤ eval x (p i)))) :=
    (measurable_of_finite b).comp (Measurable.of_eval hcoord)
  have heq : A = (fun x : Fin n → ℝ => b (fun i => decide (0 ≤ eval x (p i)))) ⁻¹' {true} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hb x
  rw [heq]
  exact hmeas (measurableSet_singleton true)

theorem Fmt.nonneg_H {n : ℕ} {H : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : Fmt n H D A) :
    0 ≤ H := by
  obtain ⟨m, hm, -⟩ := h
  exact (Nat.cast_nonneg m).trans hm

end Submission.Obl.k4_horizon_asymptotic_assembly.Outer
