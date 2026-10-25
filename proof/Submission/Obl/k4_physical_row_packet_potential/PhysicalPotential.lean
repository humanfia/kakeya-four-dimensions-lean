-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/PhysicalPotential.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
import Submission.Obl.k4_physical_row_packet_potential.LongRows

namespace Submission.Obl.k4_physical_row_packet_potential

open Set MeasureTheory MvPolynomial
open scoped BigOperators

noncomputable section

namespace PotentialFits

def gradientBudget (D : ℕ) (U curl : ℝ) : ℝ :=
  ((D + 1 : ℕ) : ℝ) ^ 2 * 3 * (max 1 (3 * U)) ^ D * curl

private theorem contraction_bound (a b w : Fin 3 → ℝ) {E V : ℝ}
    (hE : 0 ≤ E) (_hV : 0 ≤ V) (hab : ∀ i, |a i - b i| ≤ E)
    (hw : ∀ i, |w i| ≤ V) :
    |(∑ i : Fin 3, a i * w i) - (∑ i : Fin 3, b i * w i)| ≤ 3 * E * V := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 3, |a i * w i - b i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, E * V := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sub_mul, abs_mul]
      exact mul_le_mul (hab i) (hw i) (abs_nonneg _) hE
    _ = 3 * E * V := by simp; ring

/-- Radial integration in physical height units supplies the entire
own-intercept variation on each original line. Only the derivative of the
parent signal is compared with the field; its absolute normalized height
is never bounded. -/
theorem physical_potential_of_curl (Tfield : Row) (D : ℕ)
    (hdegree : ∀ i, (Tfield i).totalDegree ≤ D)
    {A curl E U V : ℝ} (hA : 0 ≤ A) (hcurl : 0 ≤ curl) (hE : 0 ≤ E)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hcoeff : ∀ i e, |(Tfield i).coeff e| ≤ A)
    (hskew : ∀ i j e, |(pderiv j (Tfield i) - pderiv i (Tfield j)).coeff e| ≤ curl)
    (T j : ℕ) (c u : P2) (P : Po) (Lines : Set Ln)
    (hbase : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T),
      ∀ i, |packetBase T j c u (l, t) i| ≤ U)
    (hvelocity : ∀ l ∈ Lines, ∀ i, |direction l i| ≤ V)
    (hrow : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T),
      |ParentSignal.rate P l t - ∑ i : Fin 3,
        eval (fun i => packetBase T j c u (l, t) i) (Tfield i) * direction l i| ≤ E) :
    ∃ Pot : MvPolynomial (Fin 3) ℝ,
      Pot.totalDegree ≤ D + 1 ∧
      (∀ e, |Pot.coeff e| ≤ (((D + 1 : ℕ) : ℝ) * 3 * A) * clock T) ∧
      ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T),
        |(eval (xp l t) P - eval (fun i => packetBase T j c u (l, t) i) Pot) -
          (eval (xp l (start T j)) P -
            eval (fun i => packetBase T j c u (l, start T j) i) Pot)| ≤
          clock T * (E + 3 * gradientBudget D U curl * V) := by
  let Q := Submission.Lib.K4CubicTests.polynomialRadialPotential Tfield D
  refine ⟨C (clock T) * Q, ?_, ?_, ?_⟩
  · exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using
        Submission.Lib.K4CubicTests.polynomialRadialPotential_totalDegree_le Tfield D)
  · intro e
    rw [coeff_C_mul, abs_mul, abs_of_pos (clock_pos T)]
    exact (mul_le_mul_of_nonneg_left (radial_coeff_le Tfield D hA hcoeff e)
      (clock_pos T).le).trans_eq (mul_comm _ _)
  · intro l hl t ht
    have hbudget : 0 ≤ gradientBudget D U curl := by unfold gradientBudget; positivity
    have hgradient (s : ℝ) (hs : s ∈ Icc (start T j) (start T j + clock T)) (i : Fin 3) :
        |eval (fun i => packetBase T j c u (l, s) i) (pderiv i Q) -
          eval (fun i => packetBase T j c u (l, s) i) (Tfield i)| ≤ gradientBudget D U curl := by
      exact Submission.Lib.K4CubicTests.polynomialRadialPotential_eval_error_le
        Tfield D hdegree curl U hcurl hU hskew _ (hbase l hl s hs) i
    have hbound (s : ℝ) (hs : s ∈ Icc (start T j) (start T j + clock T)) :
        |ParentSignal.rate P l s - ∑ i : Fin 3,
          eval (fun i => packetBase T j c u (l, s) i) (pderiv i Q) * direction l i| ≤
          E + 3 * gradientBudget D U curl * V := by
      have hc := contraction_bound
        (fun i => eval (fun i => packetBase T j c u (l, s) i) (Tfield i))
        (fun i => eval (fun i => packetBase T j c u (l, s) i) (pderiv i Q))
        (direction l) hbudget hV
        (fun i => by rw [abs_sub_comm]; exact hgradient s hs i) (hvelocity l hl)
      exact (abs_sub_le _ _ _).trans (add_le_add (hrow l hl s hs) hc)
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Icc (start T j) (start T j + clock T))
      (x := start T j) (y := t)
      (f := fun s => eval (xp l s) P -
        eval (fun i => packetBase T j c u (l, s) i) (C (clock T) * Q))
      (f' := fun s => ParentSignal.rate P l s - ∑ i : Fin 3,
        eval (fun i => packetBase T j c u (l, s) i) (pderiv i Q) * direction l i)
      (fun s hs => ((ParentSignal.hasDerivAt_signal P l s).sub
        (hasDerivAt_scaled_potential T j c u l Q s)).hasDerivWithinAt)
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s hs)
      (convex_Icc _ _) (by constructor <;> linarith [clock_pos T]) ht
    have htime : |t - start T j| ≤ clock T := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    have hm : 0 ≤ E + 3 * gradientBudget D U curl * V := by positivity
    simp only [Real.norm_eq_abs] at hmean
    exact hmean.trans
      ((mul_le_mul_of_nonneg_left htime hm).trans_eq (mul_comm _ _))

/-- The two potential clauses of the frozen packet, with the qualification
duration and all numerical losses explicit. The sets of qualification times
belong to the original lines; they are used before taking whole-block fits. -/
theorem physical_potential_from_qualified_rows (Tfield : Row) (D : ℕ)
    (hdegree : ∀ i, (Tfield i).totalDegree ≤ D)
    {A curl err U V K a ζ η : ℝ}
    (hA : 0 ≤ A) (hcurl : 0 ≤ curl) (herr : 0 ≤ err) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hcoeff : ∀ i e, |(Tfield i).coeff e| ≤ A)
    (hskew : ∀ i j e, |(pderiv j (Tfield i) - pderiv i (Tfield j)).coeff e| ≤ curl)
    (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
    (Lines : Set Ln) (times : Ln → Set ℝ)
    (hbase : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T),
      ∀ i, |packetBase T j c u (l, t) i| ≤ U)
    (hvelocity : ∀ l ∈ Lines, ∀ i, |direction l i| ≤ V)
    (htimes : ∀ l ∈ Lines, times l ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal η ≤ volume (times l))
    (hfit : ∀ l ∈ Lines, ∀ s ∈ times l,
      |ParentSignal.rate P l (start T j + clock T * s) - ∑ i : Fin 3,
        direction l i * eval (fun i => packetBase T j c u (l, start T j + clock T * s) i)
          (Tfield i)| ≤ err)
    (hcoeffBudget : ((D + 1 : ℕ) : ℝ) * 3 * A ≤ K)
    (herrorBudget : clock T *
      ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err + 3 * gradientBudget D U curl * V) ≤ a * ζ) :
    ∃ Pot : MvPolynomial (Fin 3) ℝ,
      Pot.totalDegree ≤ D + 1 ∧ (∀ e, |Pot.coeff e| ≤ K * clock T) ∧
      ∀ l ∈ Lines, ∀ t ∈ Icc ((j : ℝ) * clock T) (((j : ℝ) + 1) * clock T),
        |(eval (xp l t) P - eval (fun i => packetBase T j c u (l, t) i) Pot) -
          (eval (xp l ((j : ℝ) * clock T)) P -
            eval (fun i => packetBase T j c u (l, (j : ℝ) * clock T) i) Pot)| ≤ a * ζ := by
  have hfull l (hl : l ∈ Lines) := whole_block_row_of_long_times Tfield D hdegree
    T j c u P hP l (times l) hη hη1 herr (htimes l hl).1 (htimes l hl).2 (hfit l hl)
  obtain ⟨Pot, hdegreePot, hcoeffPot, hvariation⟩ := physical_potential_of_curl Tfield D hdegree
    hA hcurl (show 0 ≤ (8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err by positivity)
    hU hV hcoeff hskew T j c u P Lines hbase hvelocity
    (fun l hl t ht => by simpa only [mul_comm] using hfull l hl t ht)
  refine ⟨Pot, hdegreePot, ?_, ?_⟩
  · intro e
    exact (hcoeffPot e).trans
      (mul_le_mul_of_nonneg_right hcoeffBudget (clock_pos T).le)
  · intro l hl t ht
    have ht' : t ∈ Icc (start T j) (start T j + clock T) := by
      simpa only [start, add_mul, one_mul] using ht
    exact (hvariation l hl t ht').trans herrorBudget

end PotentialFits

end

end Submission.Obl.k4_physical_row_packet_potential
