import Submission.Obl.k4_physical_parent_potential_candidates.FubiniFrame
import Submission.Lib.K4ChartLifting.PolyAlgebra

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

namespace FubiniQuadric

abbrev Poly := MvPolynomial (Fin 4) ℝ

def baseLinear (b : Fin 3 → ℝ) : Poly := ∑ i : Fin 3, C (b i)*X i.castSucc

def baseQuadratic (H : Matrix (Fin 3) (Fin 3) ℝ) : Poly :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (H i j)*X i.castSucc*X j.castSucc

def height (f0 : ℝ) (g0 : Fin 3 → ℝ) : Poly := X 3-C f0-baseLinear g0

/-- The actual degree-two polynomial obtained by freezing a Fubini frame. -/
def quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (lam : ℝ) : Poly :=
  C rho*(C 2*height f0 g0-baseQuadratic H-C 2*baseLinear m*height f0 g0-
    C lam*(height f0 g0)^2)

theorem degree_baseLinear (b : Fin 3 → ℝ) : (baseLinear b).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (isHomogeneous_C_mul_X _ _).totalDegree_le

theorem degree_baseQuadratic (H : Matrix (Fin 3) (Fin 3) ℝ) :
    (baseQuadratic H).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  exact ((isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X ℝ _)).totalDegree_le

theorem degree_height (f0 : ℝ) (g0 : Fin 3 → ℝ) : (height f0 g0).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (max_le
    ((totalDegree_sub _ _).trans (max_le (by simp) (by simp))) (degree_baseLinear _))

theorem degree_quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (lam : ℝ) :
    (quadric rho f0 g0 H m lam).totalDegree ≤ 2 := by
  have hk := degree_height f0 g0
  have hb := degree_baseLinear m
  have htwo (a : ℝ) (P : Poly) : (C a*P).totalDegree ≤ P.totalDegree := by
    simpa only [totalDegree_C, zero_add] using totalDegree_mul (C a) P
  unfold quadric
  apply (htwo _ _).trans
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_sub _ _).trans (max_le ((htwo _ _).trans (by omega)) (degree_baseQuadratic _))
    · exact (totalDegree_mul _ _).trans (by have := (htwo 2 (baseLinear m)).trans hb; omega)
  · exact (htwo _ _).trans ((totalDegree_pow _ _).trans (by omega))

theorem eval_baseLinear (b u : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc u w) (baseLinear b) = ∑ i : Fin 3, b i*u i := by
  simp [baseLinear]

theorem eval_baseQuadratic (H : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc u w) (baseQuadratic H) = ∑ i : Fin 3, ∑ j : Fin 3, u i*H i j*u j := by
  simp only [baseQuadratic, map_sum, map_mul, eval_C, eval_X, Fin.snoc_castSucc]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem eval_height (f0 : ℝ) (g0 u : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc u w) (height f0 g0) = w-f0-∑ i : Fin 3, g0 i*u i := by
  simp only [height, map_sub, eval_X, eval_C, eval_baseLinear]
  rfl

theorem eval_quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m u : Fin 3 → ℝ) (lam w : ℝ) :
    eval (Fin.snoc u w) (quadric rho f0 g0 H m lam) =
      fubiniFrameValue rho (w-f0-∑ i : Fin 3, g0 i*u i)
        (∑ i : Fin 3, ∑ j : Fin 3, u i*H i j*u j) (∑ i : Fin 3, m i*u i) lam := by
  simp only [quadric, map_mul, map_sub, map_pow, eval_C,
    eval_height, eval_baseLinear, eval_baseQuadratic, fubiniFrameValue]

theorem pderiv_baseLinear (b : Fin 3 → ℝ) : pderiv (3:Fin 4) (baseLinear b) = 0 := by
  simp [baseLinear, Fin.sum_univ_three, pderiv_C_mul, pderiv_X, Pi.single_apply]

theorem pderiv_baseQuadratic (H : Matrix (Fin 3) (Fin 3) ℝ) :
    pderiv (3:Fin 4) (baseQuadratic H) = 0 := by
  simp [baseQuadratic, Fin.sum_univ_three, pderiv_mul, pderiv_C_mul, pderiv_X, Pi.single_apply]

theorem pderiv_height (f0 : ℝ) (g0 : Fin 3 → ℝ) : pderiv (3:Fin 4) (height f0 g0) = 1 := by
  simp [height, pderiv_baseLinear, pderiv_X, Pi.single_apply]

theorem pderiv_quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (lam : ℝ) :
    pderiv (3:Fin 4) (quadric rho f0 g0 H m lam) =
      C rho*(C 2-C 2*baseLinear m-C (2*lam)*height f0 g0) := by
  have htwo : pderiv (3:Fin 4) (2:Poly) = 0 := by
    change pderiv (3:Fin 4) (C (2:ℝ)) = 0
    exact pderiv_C
  simp only [quadric, map_sub, pderiv_C_mul, pderiv_baseQuadratic, pderiv_baseLinear,
    pderiv_height, pderiv_mul, pderiv_C, pderiv_pow, htwo, map_ofNat, Nat.cast_ofNat, pow_one,
    mul_one, zero_mul, add_zero, zero_add, sub_zero]
  simp only [map_mul, map_ofNat]
  ring

theorem eval_pderiv_quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m u : Fin 3 → ℝ) (lam w : ℝ) :
    eval (Fin.snoc u w) (pderiv (3:Fin 4) (quadric rho f0 g0 H m lam)) =
      fubiniFrameVertical rho (w-f0-∑ i : Fin 3, g0 i*u i) (∑ i : Fin 3, m i*u i) lam := by
  simp only [pderiv_quadric, map_mul, map_sub, eval_C, eval_height, eval_baseLinear,
    fubiniFrameVertical]

theorem pderiv_twice_quadric (rho f0 : ℝ) (g0 : Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ) (lam : ℝ) :
    pderiv (3:Fin 4) (pderiv (3:Fin 4) (quadric rho f0 g0 H m lam)) = C (-2*rho*lam) := by
  rw [pderiv_quadric]
  simp only [pderiv_C_mul, map_sub, pderiv_C, pderiv_baseLinear, pderiv_height,
    mul_zero, mul_one, sub_zero, zero_sub]
  simp only [← map_mul, ← map_neg]
  congr 1
  ring


theorem mass_baseLinear {Z : ℝ} (hZ : 0 ≤ Z) (b : Fin 3 → ℝ)
    (hb : ∀ i, |b i| ≤ Z) : coeffL1 (baseLinear b) ≤ 3*Z := by
  have hsum := coeffL1_sum_le Finset.univ (fun i : Fin 3 => (C (b i)*X i.castSucc : Poly))
  apply hsum.trans
  calc
    _ ≤ ∑ _i : Fin 3, Z := Finset.sum_le_sum fun i _ => by
      exact ((coeffL1_C_mul_le _ _).trans (by rw [coeffL1_X, mul_one])).trans (hb i)
    _ = _ := by simp

theorem mass_baseQuadratic {Z : ℝ} (hZ : 0 ≤ Z) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ∀ i j, |H i j| ≤ Z) : coeffL1 (baseQuadratic H) ≤ 9*Z := by
  have hterm (i j : Fin 3) : coeffL1 (C (H i j)*X i.castSucc*X j.castSucc : Poly) ≤ Z := by
    apply (coeffL1_mul_le _ _).trans
    rw [coeffL1_X, mul_one]
    exact ((coeffL1_C_mul_le _ _).trans (by rw [coeffL1_X, mul_one])).trans (hH i j)
  have hinner (i : Fin 3) :
      coeffL1 (∑ j : Fin 3, (C (H i j)*X i.castSucc*X j.castSucc : Poly)) ≤ 3*Z := by
    apply (coeffL1_sum_le Finset.univ _).trans
    calc
      _ ≤ ∑ _j : Fin 3, Z := Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := by simp
  apply (coeffL1_sum_le Finset.univ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, 3*Z := Finset.sum_le_sum fun i _ => hinner i
    _ = _ := by simp; ring

theorem mass_height {Z f0 : ℝ} (hZ : 1 ≤ Z) (g0 : Fin 3 → ℝ)
    (hf0 : |f0| ≤ Z) (hg : ∀ i, |g0 i| ≤ Z) : coeffL1 (height f0 g0) ≤ 5*Z := by
  have hZ0 : 0 ≤ Z := by linarith
  calc
    _ ≤ coeffL1 (X 3-C f0 : Poly)+coeffL1 (baseLinear g0) := coeffL1_sub_le _ _
    _ ≤ (1+Z)+3*Z := add_le_add
      ((coeffL1_sub_le _ _).trans (by rw [coeffL1_X, coeffL1_C]; linarith))
      (mass_baseLinear hZ0 g0 hg)
    _ ≤ _ := by linarith

/-- Every frozen frame has a fixed polynomial coefficient bound. -/
theorem mass_quadric {Z rho f0 lam : ℝ} (hZ : 1 ≤ Z)
    (g0 m : Fin 3 → ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hrho : |rho| ≤ Z) (hf0 : |f0| ≤ Z) (hg : ∀ i, |g0 i| ≤ Z)
    (hH : ∀ i j, |H i j| ≤ Z) (hm : ∀ i, |m i| ≤ Z) (hlam : |lam| ≤ Z) :
    coeffL1 (quadric rho f0 g0 H m lam) ≤ 74*Z^4 := by
  have hZ0 : 0 ≤ Z := by linarith
  have hk := mass_height hZ g0 hf0 hg
  have hlin := mass_baseLinear hZ0 m hm
  have hquad := mass_baseQuadratic hZ0 H hH
  have hfirst : coeffL1 (C 2*height f0 g0) ≤ 10*Z := by
    exact (coeffL1_C_mul_le _ _).trans (by norm_num; linarith)
  have hcross : coeffL1 (C 2*baseLinear m*height f0 g0) ≤ 30*Z^2 := by
    apply (coeffL1_mul_le _ _).trans
    have hc := coeffL1_C_mul_le (2:ℝ) (baseLinear m)
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)] at hc
    calc
      _ ≤ (2*(3*Z))*(5*Z) := mul_le_mul (hc.trans (by linarith)) hk (coeffL1_nonneg _) (by positivity)
      _ = _ := by ring
  have hsquare : coeffL1 (C lam*(height f0 g0)^2) ≤ 25*Z^3 := by
    apply (coeffL1_C_mul_le _ _).trans
    calc
      _ ≤ Z*(5*Z)^2 := mul_le_mul hlam
        ((coeffL1_pow_le _ _).trans (pow_le_pow_left₀ (coeffL1_nonneg _) hk 2))
        (coeffL1_nonneg _) hZ0
      _ = _ := by ring
  have hinside : coeffL1
      (C 2*height f0 g0-baseQuadratic H-C 2*baseLinear m*height f0 g0-C lam*(height f0 g0)^2) ≤
      19*Z+30*Z^2+25*Z^3 := by
    apply (coeffL1_sub_le _ _).trans
    apply add_le_add ?_ hsquare
    apply (coeffL1_sub_le _ _).trans
    apply add_le_add ?_ hcross
    exact (coeffL1_sub_le _ _).trans (by linarith)
  calc
    _ ≤ |rho| * coeffL1
        (C 2*height f0 g0-baseQuadratic H-C 2*baseLinear m*height f0 g0-C lam*(height f0 g0)^2) :=
      coeffL1_C_mul_le _ _
    _ ≤ Z*(19*Z+30*Z^2+25*Z^3) := mul_le_mul hrho hinside (coeffL1_nonneg _) hZ0
    _ ≤ 74*Z^4 := by
      have h2 : Z^2 ≤ Z^4 := pow_le_pow_right₀ hZ (by decide : 2 ≤ 4)
      have h3 : Z^3 ≤ Z^4 := pow_le_pow_right₀ hZ (by decide : 3 ≤ 4)
      nlinarith

end FubiniQuadric

end

end Submission.Obl.k4_physical_parent_potential_candidates
