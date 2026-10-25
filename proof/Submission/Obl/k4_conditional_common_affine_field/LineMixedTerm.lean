import Submission.Obl.k4_conditional_common_affine_field.Interfaces
import Submission.Lib.K4ScalarCoreAssembly.OriginalLongRows
import Submission.Lib.K4PolynomialRemez
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarCoreAssembly
open Submission.Lib.K4PolynomialRemez

noncomputable def mixedTrace (β : Fin 4 → ℝ) (b u w₁ w₂ : ℝ) (a : Fin 3 → ℝ) :
    Polynomial ℝ :=
  Polynomial.C (β 3*(u-w₁)*(u-w₂))*Polynomial.X^2 +
    Polynomial.C (β 1*(u-w₁)+β 2*(u-w₂)+β 3*b*((u-w₁)+(u-w₂))-a 1)*Polynomial.X +
    Polynomial.C (β 0+(β 1+β 2)*b+β 3*b^2-a 0)

theorem mixedTrace_degree (β : Fin 4 → ℝ) (b u w₁ w₂ : ℝ) (a : Fin 3 → ℝ) :
    (mixedTrace β b u w₁ w₂ a).natDegree ≤ 2 := by
  unfold mixedTrace
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · simpa only [pow_one] using (Polynomial.natDegree_C_mul_X_pow_le
        (β 1*(u-w₁)+β 2*(u-w₂)+β 3*b*((u-w₁)+(u-w₂))-a 1) 1).trans (by omega)
  · simp only [Polynomial.natDegree_C]
    omega

theorem mixedTrace_eval (β : Fin 4 → ℝ) (b u w₁ w₂ : ℝ) (a : Fin 3 → ℝ) (t : ℝ) :
    (mixedTrace β b u w₁ w₂ a).eval t =
      β 0+β 1*(b+t*(u-w₁))+β 2*(b+t*(u-w₂))+
        β 3*(b+t*(u-w₁))*(b+t*(u-w₂))-(a 0+a 1*t) := by
  simp only [mixedTrace,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  ring

set_option maxHeartbeats 800000 in
/-- A long original line and one recurring chart option remove the mixed term
of a dense bilinear field fit. All losses are relative to the original prior. -/
theorem lineMixedTerm : LineMixedTerm := by
  intro α _ ν μ ι chart L b u g E β K n m r E₁ E₂ w₁ w₂ hν hK hn hm hr
    hdom hEm hEtime hmass hL hbilin hfit haway
  classical
  letI : IsProbabilityMeasure ν := hν
  obtain ⟨T,hTm,hTE,hTmass,hTrow⟩ := exists_original_long_rows ν μ K m hK hm
    hdom E hEm (by simpa only [measure_univ,mul_one] using hmass)
  have hμT : μ T ≠ 0 := by
    have h : ENNReal.ofReal (m/2) ≤ μ T := by
      simpa only [measure_univ,mul_one] using hTmass
    exact ((ENNReal.ofReal_pos.mpr (by positivity)).trans_le h).ne'
  obtain ⟨p,hpT⟩ := nonempty_of_measure_ne_zero hμT
  have hpE := hTE hpT
  let ell := p.1
  let row : Set ℝ := Prod.mk ell ⁻¹' E
  have hrowm : MeasurableSet row := hEm.preimage (measurable_const.prodMk measurable_id)
  have hrowtime : row ⊆ Icc (0 : ℝ) 1 := fun t ht => (hEtime ht).2
  have hrowmass : ENNReal.ofReal (m/(2*K)) ≤ volume row := hTrow p hpT
  let P (a : Fin 3 → ℝ) := mixedTrace β (b ell) (u ell) w₁ w₂ a
  have hpolyfit (t : ℝ) (ht : t ∈ row) (a : Fin 3 → ℝ)
      (ha : |g (ell,t)-a 0-a 1*t| ≤ E₂) : |(P a).eval t| ≤ E₁+E₂ := by
    have h₁ := hbilin (ell,t) ht
    have h₂ : |g (ell,t)-(a 0+a 1*t)| ≤ E₂ := by
      simpa only [sub_add_eq_sub_sub] using ha
    rw [mixedTrace_eval]
    apply (abs_sub_le _ (g (ell,t)) _).trans
    exact add_le_add (by simpa only [abs_sub_comm] using h₁) h₂
  obtain ⟨a₀,ha₀,hf₀⟩ := hfit p hpE
  have hE₁ : 0 ≤ E₁ := (abs_nonneg _).trans (hbilin p hpE)
  have hE₂ : 0 ≤ E₂ := (abs_nonneg _).trans hf₀
  let A (a : Fin 3 → ℝ) : Set ℝ := row ∩ {t | |(P a).eval t| ≤ E₁+E₂}
  have hAm (a : Fin 3 → ℝ) : MeasurableSet (A a) := by
    have hpm : Measurable (fun t : ℝ => |(P a).eval t|) := by fun_prop
    exact hrowm.inter (measurableSet_le hpm measurable_const)
  have hcover : row ⊆ ⋃ a ∈ L (chart ell), A a := by
    intro t ht
    obtain ⟨a,ha,hfa⟩ := hfit (ell,t) ht
    exact mem_iUnion₂.mpr ⟨a,ha,ht,hpolyfit t ht a hfa⟩
  have hLn : (L (chart ell)).Nonempty := ⟨a₀,ha₀⟩
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image (L (chart ell)) (fun a => volume (A a)) hLn
  have hnpos : 0 < n := by linarith
  have hcard : ((L (chart ell)).card : ℝ≥0∞) ≤ ENNReal.ofReal n := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hL (chart ell))
  have hlong : ENNReal.ofReal (m/(2*K)) ≤ ENNReal.ofReal n*volume (A a) := by
    calc
      _ ≤ volume row := hrowmass
      _ ≤ volume (⋃ a ∈ L (chart ell), A a) := measure_mono hcover
      _ ≤ ∑ a ∈ L (chart ell), volume (A a) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ L (chart ell), volume (A a) := Finset.sum_le_sum fun a' ha' => hmax a' ha'
      _ = ((L (chart ell)).card : ℝ≥0∞)*volume (A a) := by simp
      _ ≤ ENNReal.ofReal n*volume (A a) := mul_le_mul' hcard le_rfl
  let η := m/(2*K*n)
  have hη : 0 < η := by dsimp [η]; positivity
  have hAmass : ENNReal.ofReal η ≤ volume (A a) := by
    have heq : ENNReal.ofReal η = ENNReal.ofReal (m/(2*K))/ENNReal.ofReal n := by
      rw [← ENNReal.ofReal_div_of_pos hnpos]
      congr 1
      dsimp [η]
      ring
    rw [heq]
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hnpos).ne' ENNReal.ofReal_ne_top).mpr
      (by simpa only [mul_comm] using hlong)
  have hAtime : A a ⊆ Icc (0 : ℝ) 1 := fun t ht => hrowtime ht.1
  have hη1 : η ≤ 1 := by
    have h := hAmass.trans (measure_mono hAtime)
    have hh : ENNReal.ofReal η ≤ ENNReal.ofReal (1 : ℝ) := by simpa using h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp hh
  have hsup := polynomial_remez_unit (P a) 2 (mixedTrace_degree _ _ _ _ _ _)
    (A a) hη hη1 (add_nonneg hE₁ hE₂) hAtime hAmass (fun t ht => ht.2)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |(P a).eval t| ≤ (48*K*n/m)^2*(E₁+E₂) := by
    have hfactor : 8*((2 : ℝ)+1)/η = 48*K*n/m := by
      dsimp [η]
      field_simp
      ring
    simpa only [Nat.cast_ofNat,hfactor] using hsup
  let c : Fin 6 → ℝ :=
    ![β 0+(β 1+β 2)*b ell+β 3*(b ell)^2-a 0,
      β 1*(u ell-w₁)+β 2*(u ell-w₂)+β 3*b ell*((u ell-w₁)+(u ell-w₂))-a 1,
      0,β 3*(u ell-w₁)*(u ell-w₂),0,0]
  have hcoeff := Submission.Obl.k4_fixed_budget_quadratic_recovery.quadratic_coefficients_bound
    (c := c) (H := (48*K*n/m)^2*(E₁+E₂)) (by
      intro t ht z hz
      have h := hbound t ht
      simpa [Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue,
        c,P,mixedTrace,add_comm,add_left_comm,add_assoc] using h) (3 : Fin 6)
  change |β 3*(u ell-w₁)*(u ell-w₂)| ≤ 8*((48*K*n/m)^2*(E₁+E₂)) at hcoeff
  have hsep := haway p hpE
  calc
    |β 3| * r^2 ≤ |β 3| * (|u ell-w₁| * |u ell-w₂|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [pow_two] using mul_le_mul hsep.1 hsep.2 hr.le (abs_nonneg _)
    _ = |β 3*(u ell-w₁)*(u ell-w₂)| := by rw [abs_mul,abs_mul]; ring
    _ ≤ 8*((48*K*n/m)^2*(E₁+E₂)) := hcoeff
    _ = _ := by ring

end Submission.Obl.k4_conditional_common_affine_field
