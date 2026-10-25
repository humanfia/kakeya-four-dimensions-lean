/- Adapted within this LOT tree from o218/x0760, commit 25c3c14905bb62f173baf14705e87045cdbb0e5b,
Submission/Obl/k4_horizontal_endpoint_wide_return/GraphReturn.lean. -/
import Mathlib
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MvPolynomial Submission.Lib.K4ChartLifting Submission.Lib.K4ContactNormalization MeasureTheory Set

noncomputable section

/-- Include a polynomial in the true base coordinates into all four coordinates. -/
def baseSubstitution : Fin 3 → MvPolynomial (Fin 4) ℝ := fun i => X i.castSucc

/-- A graph test with its native hidden derivative fixed to one. -/
def baseGraphTest (G : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℝ :=
  baseCalibratedTest (X 3) G

theorem baseGraphTest_degree (G : MvPolynomial (Fin 3) ℝ) (hG : G.totalDegree ≤ 2) :
    (baseGraphTest G).totalDegree ≤ 2 :=
  baseCalibratedTest_degree (by simp) hG

theorem baseGraphTest_pderiv (G : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (baseGraphTest G) = 1 := by
  simpa [baseGraphTest] using pderiv_baseCalibratedTest (X 3) G

theorem baseGraphTest_pderiv_pderiv (G : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (baseGraphTest G)) = 0 := by
  rw [baseGraphTest_pderiv]
  simp

theorem eval_baseGraphTest (G : MvPolynomial (Fin 3) ℝ) (x : Fin 4 → ℝ) :
    eval x (baseGraphTest G) = x 3 - eval (fun i : Fin 3 => x i.castSucc) G := by
  simpa only [baseGraphTest, eval_X, Function.comp_def] using eval_baseCalibratedTest (X 3) G x

theorem baseGraphTest_coeffL1 (G : MvPolynomial (Fin 3) ℝ) :
    coeffL1 (baseGraphTest G) ≤ 1 + coeffL1 G := by
  have heq : rename Fin.castSucc G = bind₁ baseSubstitution G := by
    rw [rename_eq_aeval]
    rfl
  have hsubst : coeffL1 (rename Fin.castSucc G) ≤ coeffL1 G := by
    rw [heq]
    simpa only [one_pow, mul_one] using coeffL1_bind₁_le baseSubstitution 1 le_rfl
      (by intro i; simp [baseSubstitution, coeffL1_X]) G
  exact (coeffL1_sub_le _ _).trans (by rw [coeffL1_X]; gcongr)

/-- The graph polynomial's coefficient bound is independent of hidden fits. -/
theorem baseGraphTest_coeff (G : MvPolynomial (Fin 3) ℝ) (e : Fin 4 →₀ ℕ) :
    |(baseGraphTest G).coeff e| ≤ 1 + coeffL1 G :=
  (abs_coeff_le_coeffL1 _ _).trans (baseGraphTest_coeffL1 G)

/-- A full-block prediction gives all three native fit inequalities at once. -/
theorem baseGraphTest_fit {α : Type*} (x : α → ℝ → Fin 4 → ℝ)
    (G : MvPolynomial (Fin 3) ℝ) {H a : ℝ} (hH : 1 ≤ H) (ha : 0 < a)
    (l : α) (I : Set ℝ)
    (hfit : ∀ t ∈ I,
      |(x l t) 3 - eval (fun i : Fin 3 => (x l t) i.castSucc) G| ≤ H * a) :
    ∀ t ∈ I, |eval (x l t) (baseGraphTest G)| ≤ H * a ∧
      |eval (x l t) (pderiv (3 : Fin 4) (baseGraphTest G))| ≤ H ∧
      |eval (x l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (baseGraphTest G)))| ≤ H / a := by
  intro t ht
  rw [eval_baseGraphTest, baseGraphTest_pderiv_pderiv, baseGraphTest_pderiv]
  simp only [map_one, abs_one, map_zero, abs_zero]
  exact ⟨hfit t ht, hH, div_nonneg (le_trans zero_le_one hH) ha.le⟩

/-- Any finite polynomial bound is in the frozen homogeneous coefficient budget. -/
theorem homogeneous_coefficient_budget {N R : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    {Q : MvPolynomial (Fin 4) ℝ} (hQ : ∀ e, |Q.coeff e| ≤ N ^ R)
    (F P : MvPolynomial (Fin 4) ℝ) :
    ∀ e, |Q.coeff e| ≤ N ^ R *
      ((1 + ∑ e ∈ F.support, |F.coeff e|) + ∑ e ∈ P.support, |P.coeff e|) ^ R := by
  intro e
  have hbase : (1 : ℝ) ≤
      (1 + ∑ e ∈ F.support, |F.coeff e|) + ∑ e ∈ P.support, |P.coeff e| := by
    have hF := Finset.sum_nonneg (fun e (_ : e ∈ F.support) => abs_nonneg (F.coeff e))
    have hP := Finset.sum_nonneg (fun e (_ : e ∈ P.support) => abs_nonneg (P.coeff e))
    linarith
  have hpow : 1 ≤
      ((1 + ∑ e ∈ F.support, |F.coeff e|) + ∑ e ∈ P.support, |P.coeff e|) ^ R :=
    Real.one_le_rpow hbase hR
  exact (hQ e).trans (le_mul_of_one_le_right (Real.rpow_nonneg (zero_le_one.trans hN) R) hpow)

/-- Convert an original-law graph prediction into the exact polynomial disjunct
of the frozen candidate assertion, without changing the reference prior or law. -/
theorem native_candidate_of_graph_mass {α : Type*} [MeasurableSpace α]
    (x : α → ℝ → Fin 4 → ℝ) (ν : Measure α) (ρ : Measure (α × ℝ))
    (A B : Set α) (I : Set ℝ) (E : Set (α × ℝ))
    (N d s v ε R₀ : ℝ) (T : ℕ) (hN : 2 ≤ N) (hε : 0 < ε) (hR₀ : 0 ≤ R₀)
    (F P : MvPolynomial (Fin 4) ℝ) (G : MvPolynomial (Fin 3) ℝ)
    (hdeg : G.totalDegree ≤ 2) (hnorm : coeffL1 G ≤ N ^ R₀)
    (hE : ∀ p ∈ E, p.1 ∈ B ∧ p.2 ∈ I ∧ ∀ t ∈ I,
      |(x p.1 t) 3 - eval (fun i : Fin 3 => (x p.1 t) i.castSucc) G| ≤
        N ^ ε * N ^ (-s - v))
    (hmass : ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * ν A ≤ ρ E) :
    ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ N ^ (R₀ + 2) *
        ((1 + ∑ e ∈ F.support, |F.coeff e|) + ∑ e ∈ P.support, |P.coeff e|) ^ (R₀ + 2)) ∧
      ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * ν A ≤
        ρ {p | p.1 ∈ B ∧ p.2 ∈ I ∧
          (∀ t ∈ I, |eval (x p.1 t) Q| ≤ N ^ ε * N ^ (-s - v) ∧
            |eval (x p.1 t) (pderiv (3 : Fin 4) Q)| ≤ N ^ ε ∧
            |eval (x p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤
              N ^ ε / N ^ (-s - v)) ∧
          N ^ (-ε) ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) Q)|} := by
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hpower : ∀ e, |(baseGraphTest G).coeff e| ≤ N ^ (R₀ + 2) := by
    intro e
    calc
      |(baseGraphTest G).coeff e| ≤ 1 + coeffL1 G := baseGraphTest_coeff G e
      _ ≤ 1 + N ^ R₀ := add_le_add le_rfl hnorm
      _ ≤ 2 * N ^ R₀ := by linarith [Real.one_le_rpow hN1 hR₀]
      _ ≤ N ^ R₀ * N ^ 2 := by
        have hsq : (2 : ℝ) ≤ N ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hNpos.le R₀)]
      _ = N ^ (R₀ + 2) := by rw [Real.rpow_add hNpos, Real.rpow_two]
  refine ⟨baseGraphTest G, baseGraphTest_degree G hdeg,
    homogeneous_coefficient_budget hN1 (by linarith) hpower F P, hmass.trans ?_⟩
  apply measure_mono
  intro p hp
  obtain ⟨hpB, hpI, hpfit⟩ := hE p hp
  refine ⟨hpB, hpI, ?_, ?_⟩
  · exact baseGraphTest_fit x G (Real.one_le_rpow hN1 hε.le)
      (Real.rpow_pos_of_pos hNpos _) p.1 I hpfit
  · rw [baseGraphTest_pderiv]
    simp only [map_one, abs_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

end

end Submission.Obl.k4_horizontal_wide_interval_return
