import Mathlib
import Submission.Lib.K4XInterface.Basic

/-!
Adapted from: here:o114 (session x0383). The standalone Boolean closure kernels
are adapted within this tree from o089 BooleanFormat and o028 Signs/Families.

Fixed source sections and finite lookup tables preserve the frozen polynomial
format. The atom budget of a finite union grows linearly in its table size.
-/

namespace Submission.Lib.K4RepresentativeAssembly

open Set MvPolynomial

abbrev fmt := Submission.Lib.K4XInterface.gfmt

theorem fmt_mono {n D D' : ℕ} {H H' : ℝ} {A : Set (Fin n → ℝ)}
    (hA : fmt n H D A) (hH : H ≤ H') (hD : D ≤ D') : fmt n H' D' A := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := hA
  exact ⟨m, hm.trans hH, p, fun i => (hp i).trans hD, b, hb⟩

theorem fmt_compl {n D : ℕ} {H : ℝ} {A : Set (Fin n → ℝ)} (hA : fmt n H D A) :
    fmt n H D Aᶜ := by
  classical
  obtain ⟨m, hm, p, hp, b, hb⟩ := hA
  refine ⟨m, hm, p, hp, fun v => !(b v), ?_⟩
  intro x
  change (¬ x ∈ A) ↔ (! b (fun i => decide (0 ≤ eval x (p i)))) = true
  rw [hb x]
  cases b (fun i => decide (0 ≤ eval x (p i))) <;> decide

theorem fmt_inter {n D D' : ℕ} {H H' : ℝ} {A B : Set (Fin n → ℝ)}
    (hA : fmt n H D A) (hB : fmt n H' D' B) :
    fmt n (H + H') (max D D') (A ∩ B) := by
  classical
  obtain ⟨m, hm, p, hp, b, hb⟩ := hA
  obtain ⟨m', hm', p', hp', b', hb'⟩ := hB
  refine ⟨m+m', by exact_mod_cast add_le_add hm hm', Fin.addCases p p', ?_,
    fun v => b (fun i => v (Fin.castAdd m' i)) && b' (fun i => v (Fin.natAdd m i)), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (hp j).trans (le_max_left D D')
    · simpa only [Fin.addCases_right] using (hp' j).trans (le_max_right D D')
  · intro x
    simp only [mem_inter_iff, Bool.and_eq_true, Fin.addCases_left, Fin.addCases_right]
    exact and_congr (hb x) (hb' x)

theorem fmt_union {n D D' : ℕ} {H H' : ℝ} {A B : Set (Fin n → ℝ)}
    (hA : fmt n H D A) (hB : fmt n H' D' B) :
    fmt n (H + H') (max D D') (A ∪ B) := by
  have hh := fmt_compl (fmt_inter (fmt_compl hA) (fmt_compl hB))
  simpa only [Set.compl_inter, compl_compl] using hh

theorem fmt_empty (n D : ℕ) : fmt n 0 D ∅ := by
  refine ⟨0, by simp, Fin.elim0, (fun i => Fin.elim0 i), fun _ => false, ?_⟩
  intro x
  simp

private theorem degree_aeval_linear_le {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [aeval_def, eval₂]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  change (C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree
  have hfirst := totalDegree_mul (C (p.coeff d)) (∏ i ∈ d.support, f i ^ d i)
  rw [totalDegree_C, zero_add] at hfirst
  apply hfirst.trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := le_totalDegree hd

private theorem eval_aeval_real {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simpa only [map_add] using congrArg₂ (fun a b : ℝ => a+b) hp hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, eval_mul, eval_X, hp]

theorem fmt_affine_preimage {n m D : ℕ} {H : ℝ} {A : Set (Fin n → ℝ)}
    (hA : fmt n H D A) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) :
    fmt m H D ((fun x i => eval x (f i)) ⁻¹' A) := by
  obtain ⟨r, hr, p, hp, b, hb⟩ := hA
  refine ⟨r, hr, fun i => aeval f (p i), ?_, b, ?_⟩
  · exact fun i => (degree_aeval_linear_le (p i) f hf).trans (hp i)
  · intro x
    simpa only [mem_preimage, eval_aeval_real] using hb (fun i => eval x (f i))

/-- A finite family of old source sections has polynomial total format cost. -/
theorem fmt_iUnion {n D C : ℕ} {H : ℝ} (A : Fin C → Set (Fin n → ℝ))
    (hA : ∀ j, fmt n H D (A j)) :
    fmt n ((C : ℝ) * H) D (⋃ j, A j) := by
  induction C with
  | zero => simpa using fmt_empty n D
  | succ C ih =>
    have hh := fmt_union (hA 0) (ih (fun j => A j.succ) (fun j => hA j.succ))
    have hcost : H + (C : ℝ) * H = ((C + 1 : ℕ) : ℝ) * H := by push_cast; ring
    simpa only [Set.iUnion_fin_add_one_eq_iUnion_succ, Function.comp_def, max_self, hcost] using hh

/-- The chosen-bin table is a table of constants, so filtering its source
sections creates no new polynomial atoms. -/
theorem fmt_selected_iUnion {n D C : ℕ} {H : ℝ} {β : Type*} [DecidableEq β]
    (A : Fin C → Set (Fin n → ℝ)) (tag : Fin C → β) (b : β)
    (hH : 0 ≤ H) (hA : ∀ j, fmt n H D (A j)) :
    fmt n ((C : ℝ) * H) D (⋃ j, if tag j = b then A j else ∅) := by
  classical
  apply fmt_iUnion
  intro j
  by_cases hj : tag j = b
  · simpa only [ite_eq_left hj] using hA j
  · simp only [ite_eq_right hj]
    exact fmt_mono (fmt_empty n D) hH le_rfl

/-- Fixing the source time does not increase the number or degree of the old
incidence atoms. -/
theorem fmt_fixed_time_section {H : ℝ} {D : ℕ}
    (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (i : ℕ) (t : ℝ)
    (hF : fmt 7 H D {z : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ F}) :
    fmt 6 H D {x : Fin 6 → ℝ | ((i, x), t) ∈ F} := by
  let q : Fin 7 → MvPolynomial (Fin 6) ℝ :=
    Fin.snoc (fun j : Fin 6 => X j) (C t)
  have hlast : q 6 = C t := by
    exact @Fin.snoc_last 6 (fun _ => MvPolynomial (Fin 6) ℝ) (C t)
      (fun j : Fin 6 => X j)
  have hq : ∀ j, (q j).totalDegree ≤ 1 := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change (q 6).totalDegree ≤ 1
      rw [hlast, totalDegree_C]
      omega
    · simp [q]
  have hh := fmt_affine_preimage hF q hq
  have heq : ((fun x i => eval x (q i)) ⁻¹'
      {z : Fin 7 → ℝ | ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ F}) =
      {x : Fin 6 → ℝ | ((i, x), t) ∈ F} := by
    ext x
    change ((i, fun j : Fin 6 => eval x (q j.castSucc)), eval x (q 6)) ∈ F ↔
      ((i, x), t) ∈ F
    rw [hlast]
    simp only [q, Fin.snoc_castSucc, eval_X, eval_C]
  rw [heq] at hh
  exact hh

end Submission.Lib.K4RepresentativeAssembly
