-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_finite_load_selection.Moment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

open scoped BigOperators

namespace WangZahlLot.Obl.wz_nsp_finite_load_selection

lemma exp_le_chord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - x by linarith) hx0 (show 1 - x + x = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith

lemma exp_moment_bound {m N : ℕ} {a : ℝ} (hm : 0 < m) (x : Fin m → ℝ)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1)
    (havg : (N : ℝ) * ∑ s, x s ≤ a * (m : ℝ)) :
    ∑ f : Fin N → Fin m, Real.exp (∑ j, x (f j)) ≤
      (m : ℝ) ^ N * Real.exp ((Real.exp 1 - 1) * a) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hsum : (∑ s, Real.exp (x s)) ≤
      (m : ℝ) * Real.exp ((Real.exp 1 - 1) * ((∑ s, x s) / m)) := by
    calc
      (∑ s, Real.exp (x s)) ≤ ∑ s, (1 + (Real.exp 1 - 1) * x s) :=
        Finset.sum_le_sum fun s _ => exp_le_chord (hx s).1 (hx s).2
      _ = (m : ℝ) * (1 + (Real.exp 1 - 1) * ((∑ s, x s) / m)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
        field_simp
      _ ≤ (m : ℝ) * Real.exp ((Real.exp 1 - 1) * ((∑ s, x s) / m)) := by
        apply mul_le_mul_of_nonneg_left _ hm'.le
        linarith [Real.add_one_le_exp ((Real.exp 1 - 1) * ((∑ s, x s) / m))]
  have hmean : (N : ℝ) * ((∑ s, x s) / m) ≤ a := by
    rw [← mul_div_assoc, div_le_iff₀ hm']
    exact havg
  calc
    (∑ f : Fin N → Fin m, Real.exp (∑ j, x (f j))) =
        (∑ s, Real.exp (x s)) ^ N := by
      simp_rw [Real.exp_sum]
      exact (Fintype.sum_pow (fun s => Real.exp (x s)) N).symm
    _ ≤ ((m : ℝ) * Real.exp ((Real.exp 1 - 1) * ((∑ s, x s) / m))) ^ N :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun s _ => (Real.exp_pos _).le) hsum N
    _ = (m : ℝ) ^ N *
        Real.exp ((Real.exp 1 - 1) * ((N : ℝ) * ((∑ s, x s) / m))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ (m : ℝ) ^ N * Real.exp ((Real.exp 1 - 1) * a) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hm'.le N)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean hb)

/-- A common choice controls every row, with logarithmic dependence on the row counts. -/
lemma finite_load_selection_log {K H m N : ℕ} {a : ℝ} (hm : 0 < m)
    (X : Fin K → Fin H → Fin m → ℝ)
    (hX : ∀ k h s, 0 ≤ X k h s ∧ X k h s ≤ 1)
    (havg : ∀ k h, (N : ℝ) * ∑ s, X k h s ≤ a * (m : ℝ)) :
    ∃ f : Fin N → Fin m, ∀ k h,
      (∑ j, X k h (f j)) ≤ (Real.exp 1 - 1) * a +
        Real.log ((K : ℝ) + 1) + Real.log ((H : ℝ) + 1) := by
  classical
  have htotal :
      (∑ f : Fin N → Fin m, ∑ k, ∑ h, Real.exp (∑ j, X k h (f j))) ≤
      ∑ _f : Fin N → Fin m, (K : ℝ) * (H : ℝ) * Real.exp ((Real.exp 1 - 1) * a) := by
    calc
      _ = ∑ k, ∑ h, ∑ f : Fin N → Fin m, Real.exp (∑ j, X k h (f j)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ ≤ ∑ _k : Fin K, ∑ _h : Fin H,
          (m : ℝ) ^ N * Real.exp ((Real.exp 1 - 1) * a) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro h _
        exact exp_moment_bound hm (X k h) (hX k h) (havg k h)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Fintype.card_fun, nsmul_eq_mul, Nat.cast_pow]
        ring
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin N → Fin m)).Nonempty from
      ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩) htotal
  refine ⟨f, fun k h => Real.exp_le_exp.mp ?_⟩
  calc
    Real.exp (∑ j, X k h (f j)) ≤ ∑ h, Real.exp (∑ j, X k h (f j)) :=
      Finset.single_le_sum (f := fun h : Fin H => Real.exp (∑ j, X k h (f j)))
        (fun h _ => (Real.exp_pos _).le) (Finset.mem_univ h)
    _ ≤ ∑ k, ∑ h, Real.exp (∑ j, X k h (f j)) :=
      Finset.single_le_sum (f := fun k : Fin K => ∑ h : Fin H,
        Real.exp (∑ j, X k h (f j)))
        (fun k _ => Finset.sum_nonneg fun h _ => (Real.exp_pos _).le)
        (Finset.mem_univ k)
    _ ≤ (K : ℝ) * (H : ℝ) * Real.exp ((Real.exp 1 - 1) * a) := hf
    _ ≤ ((K : ℝ) + 1) * ((H : ℝ) + 1) * Real.exp ((Real.exp 1 - 1) * a) := by
      gcongr <;> linarith
    _ = Real.exp ((Real.exp 1 - 1) * a +
        Real.log ((K : ℝ) + 1) + Real.log ((H : ℝ) + 1)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
        Real.exp_log (by positivity)]
      ring

end WangZahlLot.Obl.wz_nsp_finite_load_selection
