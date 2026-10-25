import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellDefs
import Submission.Obl.k4_scalar_initial_true_horizon.PriorityFormat

/-! Exact half-open floor tests for the initial atlas cell formats. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open Set MvPolynomial
open scoped BigOperators

theorem Format.polynomial_Icc {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) (a b : ℝ) :
    Format n 2 D {w | eval w p ∈ Icc a b} := by
  let Q : Fin 2 → MvPolynomial (Fin n) ℝ := ![p - C a, C b - p]
  have hQ : ∀ i, (Q i).totalDegree ≤ D := by
    intro i
    fin_cases i
    · exact (totalDegree_sub _ _).trans (max_le hp (by simp))
    · exact (totalDegree_sub _ _).trans (max_le (by simp) hp)
  have h := Format.of_sign_family (by norm_num : (1 : ℝ) ≤ 2) le_rfl Q hQ
    {s | 0 ≤ s 0 ∧ 0 ≤ s 1}
  convert h using 1
  ext w
  simp only [Q, mem_Icc, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    eval_sub, eval_C, sign_nonneg_iff, sub_nonneg]

theorem Format.polynomial_Ico {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) (a b : ℝ) :
    Format n 2 D {w | eval w p ∈ Ico a b} := by
  let Q : Fin 2 → MvPolynomial (Fin n) ℝ := ![p - C a, C b - p]
  have hQ : ∀ i, (Q i).totalDegree ≤ D := by
    intro i
    fin_cases i
    · exact (totalDegree_sub _ _).trans (max_le hp (by simp))
    · exact (totalDegree_sub _ _).trans (max_le (by simp) hp)
  have h := Format.of_sign_family (by norm_num : (1 : ℝ) ≤ 2) le_rfl Q hQ
    {s | 0 ≤ s 0 ∧ s 1 = 1}
  convert h using 1
  ext w
  simp only [Q, mem_Ico, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    eval_sub, eval_C, sign_nonneg_iff, sign_eq_one_iff, sub_nonneg, sub_pos]

theorem Format.floor_polynomial {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    Format n 2 D {w | ⌊eval w p / a⌋ = m} := by
  convert Format.polynomial_Ico p hp ((m : ℝ) * a) (((m : ℝ) + 1) * a) using 1
  ext w
  rw [mem_ofPred_eq, Int.floor_eq_iff]
  simp only [le_div_iff₀ ha, div_lt_iff₀ ha, mem_ofPred_eq, mem_Ico]

theorem Format.coordinate_abs {n : ℕ} (f : Fin n) (K : ℝ) :
    Format n 2 1 {w | |w f| ≤ K} := by
  convert Format.polynomial_Icc (X f) (by simp : (X f : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1) (-K) K using 1
  ext w
  simp only [mem_ofPred_eq, eval_X, mem_Icc, abs_le]

/-- A cell in any coefficient-coordinate slice uses sixteen linear tests.
The discrete trajectory index is a constant Boolean condition on that slice. -/
theorem cellSet_coordinate_format {n : ℕ} (f : Fin 5 → Fin n)
    (Nb Kb aL q t₀ : ℝ) (ha : 0 < aL) (hq : 0 < q)
    (m : ℤ) (k : ℕ) (c : ℤ × ℤ) (z : ℕ) :
    Format n 16 1 {w | (z, fun e => w (f e)) ∈ cellSet Nb Kb aL q t₀ m k c} := by
  let H : MvPolynomial (Fin n) ℝ := X (f 2) + C t₀ * X (f 3) + C (t₀ ^ 2) * X (f 4)
  let Y : MvPolynomial (Fin n) ℝ := X (f 0) + C t₀ * X (f 1)
  let V : MvPolynomial (Fin n) ℝ := C ((2 : ℝ) ^ k) * X (f 1)
  have hadd {p p' : MvPolynomial (Fin n) ℝ} (hp : p.totalDegree ≤ 1)
      (hp' : p'.totalDegree ≤ 1) : (p + p').totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le hp hp')
  have hscale (a : ℝ) (e : Fin n) : (C a * X e : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  have hH : H.totalDegree ≤ 1 := hadd (hadd (by simp) (hscale _ _)) (hscale _ _)
  have hY : Y.totalDegree ≤ 1 := hadd (by simp) (hscale _ _)
  have hV : V.totalDegree ≤ 1 := hscale _ _
  let A : Fin 8 → Set (Fin n → ℝ) :=
    ![{w | |w (f 0)| ≤ Kb}, {w | |w (f 1)| ≤ Kb}, {w | |w (f 2)| ≤ Kb},
      {w | |w (f 3)| ≤ Kb}, {w | |w (f 4)| ≤ Kb},
      {w | ⌊(w (f 2) + t₀ * w (f 3) + t₀ ^ 2 * w (f 4)) / aL⌋ = m},
      {w | ⌊(w (f 0) + t₀ * w (f 1)) / (q / (2 : ℝ) ^ k)⌋ = c.1},
      {w | ⌊w (f 1) * (2 : ℝ) ^ k⌋ = c.2}]
  have hA : ∀ i, Format n 2 1 (A i) := by
    intro i
    fin_cases i <;> dsimp only [A]
    · exact Format.coordinate_abs _ _
    · exact Format.coordinate_abs _ _
    · exact Format.coordinate_abs _ _
    · exact Format.coordinate_abs _ _
    · exact Format.coordinate_abs _ _
    · change Format n 2 1 {w | ⌊(w (f 2) + t₀ * w (f 3) + t₀ ^ 2 * w (f 4)) / aL⌋ = m}
      simpa only [H, eval_add, eval_mul, eval_C, eval_X] using Format.floor_polynomial H hH ha m
    · change Format n 2 1 {w | ⌊(w (f 0) + t₀ * w (f 1)) / (q / (2 : ℝ) ^ k)⌋ = c.1}
      simpa only [Y, eval_add, eval_mul, eval_C, eval_X] using
        Format.floor_polynomial Y hY (div_pos hq (by positivity)) c.1
    · change Format n 2 1 {w | ⌊w (f 1) * (2 : ℝ) ^ k⌋ = c.2}
      simpa only [V, eval_mul, eval_C, eval_X, div_one, mul_comm] using
        Format.floor_polynomial V hV (by norm_num : (0 : ℝ) < 1) c.2
  have h := Format.of_membership_rule (by norm_num : (1 : ℝ) ≤ 16) (fun _ => 2) A hA
    (by norm_num) {s | (z : ℝ) ≤ Nb ∧ ∀ i, s i}
  convert h using 1
  ext w
  simp only [A, cellSet, bddTraj, xBin, cellIdx,
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.spatial,
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden,
    mem_ofPred_eq, Prod.ext_iff, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  tauto

theorem cellSet_fiber_format (Nb Kb aL q t₀ : ℝ) (ha : 0 < aL) (hq : 0 < q)
    (m : ℤ) (k : ℕ) (c : ℤ × ℤ) (z : ℕ) :
    Format 5 16 1 {w | (z, w) ∈ cellSet Nb Kb aL q t₀ m k c} :=
  cellSet_coordinate_format id Nb Kb aL q t₀ ha hq m k c z

theorem cellIncidences_fiber_format {Nb Kb aL q t₀ R : ℝ} {D : ℕ}
    (ha : 0 < aL) (hq : 0 < q) (hR : 1 ≤ R)
    (m : ℤ) (k : ℕ) (c : ℤ × ℤ) (T : ℕ) (j : Fin (2 ^ T))
    (E : Set (Trajectory × ℝ))
    (hE : ∀ z, Format 6 R D {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ E}) (z : ℕ) :
    Format 6 (R + 18) (max D 1) {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈
      E ∩ (cellSet Nb Kb aL q t₀ m k c ×ˢ I T j)} := by
  have hA := cellSet_coordinate_format Fin.castSucc Nb Kb aL q t₀ ha hq m k c z
  have ht := Format.polynomial_Icc (X (5 : Fin 6)) (by simp : (X (5 : Fin 6) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1)
    ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T)
  have hAt := hA.inter ht (by norm_num) (by norm_num)
  have h := (hE z).inter hAt hR (by norm_num)
  convert h using 1 <;> try norm_num
  ext w
  simp only [mem_ofPred_eq, mem_inter_iff, I, mem_Icc]

end Submission.Obl.k4_scalar_initial_true_horizon
