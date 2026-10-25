/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/Format.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
General finite Boolean rule and two-boundary floor test: accepted here:o148, FormatRule.lean.
Absolute-value sign test: accepted here:o115, RefinementFormat.lean. Only these generic operations are promoted here.
-/

import Submission.Lib.K4ChartLifting.Format

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MvPolynomial
open Submission.Lib.K4ChartLifting

lemma format_abs_le {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (H : ℝ) :
    Fmt 2 d {z | |eval z P| ≤ H} := by
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

theorem fmt_rule {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ)
    (hS : ∀ i, Fmt (H i) D (S i)) (rule : (ι → Prop) → Prop) :
    Fmt (∑ i, H i) D {x | rule (fun i => x ∈ S i)} := by
  classical
  choose m hm p hp b hb using hS
  let e := Fintype.equivFin (Σ i, Fin (m i))
  refine ⟨Fintype.card (Σ i, Fin (m i)), ?_,
    (fun j => p (e.symm j).1 (e.symm j).2),
    (fun j => hp (e.symm j).1 (e.symm j).2),
    (fun v => decide (rule (fun i => b i (fun j => v (e ⟨i, j⟩)) = true))), ?_⟩
  · simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hm i
  · intro x
    have hpoly (i : ι) (j : Fin (m i)) :
        p (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2 = p i j :=
      congrArg (fun z : Σ i, Fin (m i) => p z.1 z.2) (e.symm_apply_apply ⟨i, j⟩)
    simp only [mem_ofPred_eq, decide_eq_true_eq, hpoly]
    have hbits : (fun i => b i (fun j => decide (0 ≤ MvPolynomial.eval x (p i j))) = true) =
        (fun i => x ∈ S i) := by
      funext i
      exact propext (hb i x).symm
    rw [hbits]

/-- Uniformly bounded predicates give a linear test count. -/
theorem fmt_rule_uniform {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ℝ)
    (hS : ∀ i, Fmt H D (S i)) (rule : (ι → Prop) → Prop) :
    Fmt ((Fintype.card ι : ℝ) * H) D {x | rule (fun i => x ∈ S i)} := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    fmt_rule S (fun _ => H) hS rule

theorem fmt_floor_eq {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) (j : ℤ) :
    Fmt 2 D {x | ⌊MvPolynomial.eval x P⌋ = j} := by
  classical
  refine ⟨2, by norm_num, ![P - MvPolynomial.C (j : ℝ), P - MvPolynomial.C ((j : ℝ) + 1)],
    ?_, (fun v => v 0 && !(v 1)), ?_⟩
  · intro i
    fin_cases i <;> apply (MvPolynomial.totalDegree_sub _ _).trans <;>
      simpa only [MvPolynomial.totalDegree_C, max_zero] using hP
  · intro x
    simp only [mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, not_le,
      map_sub, MvPolynomial.eval_C]
    rw [Int.floor_eq_iff]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

end Submission.Lib.K4ScalarCoreTools.Finalization
