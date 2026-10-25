import Submission.Obl.k4_physical_parent_potential_candidates.FubiniQuadric

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MvPolynomial
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8000

abbrev FubiniBase := EuclideanSpace ℝ (Fin 3)

/-- A genuine differential frame on the real unit ball. Its three defect
fields are the cubic, scalar-curvature, and scalar-gradient defects. -/
structure FubiniGraphData (K ε : ℝ) where
  f : FubiniBase → ℝ
  grad : FubiniBase → Fin 3 → ℝ
  H : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ
  m : FubiniBase → Fin 3 → ℝ
  lam : FubiniBase → ℝ
  rho : FubiniBase → ℝ
  E : FubiniBase → Fin 3 → Fin 3 → Fin 3 → ℝ
  T : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ
  W : FubiniBase → Fin 3 → ℝ
  f_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, |f x| ≤ K
  grad_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i, |grad x i| ≤ K
  H_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j, |H x i j| ≤ K
  m_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i, |m x i| ≤ K
  lam_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, |lam x| ≤ K
  rho_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, |rho x| ≤ K
  E_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |E x i j k| ≤ ε
  T_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j, |T x i j| ≤ ε
  W_bound : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i, |W x i| ≤ ε
  f_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt (fun s => f (s • x)) (∑ i : Fin 3, grad (t • x) i*x i) t
  grad_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1, ∀ i,
    HasDerivAt (fun s => grad (s • x) i) (∑ j : Fin 3, H (t • x) i j*x j) t
  H_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1, ∀ i j,
    HasDerivAt (fun s => H (s • x) i j)
      (∑ k : Fin 3, (fubiniCubic (H (t • x)) (m (t • x)) k i j+E (t • x) k i j)*x k) t
  m_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1, ∀ i,
    HasDerivAt (fun s => m (s • x) i)
      (∑ k : Fin 3, (m (t • x) k*m (t • x) i+lam (t • x)*H (t • x) k i+T (t • x) k i)*x k) t
  lam_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt (fun s => lam (s • x))
      (∑ k : Fin 3, (lam (t • x)*m (t • x) k+W (t • x) k)*x k) t
  rho_deriv : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt (fun s => rho (s • x)) (-rho (t • x)*(∑ k : Fin 3, m (t • x) k*x k)) t

namespace FubiniGraphData

variable {K ε : ℝ} (data : FubiniGraphData K ε)

def frozen : MvPolynomial (Fin 4) ℝ :=
  FubiniQuadric.quadric (data.rho 0) (data.f 0) (data.grad 0) (data.H 0) (data.m 0) (data.lam 0)

theorem frozen_degree : data.frozen.totalDegree ≤ 2 := FubiniQuadric.degree_quadric _ _ _ _ _ _

theorem frozen_mass (hK : 1 ≤ K) :
    Submission.Lib.K4ChartLifting.coeffL1 data.frozen ≤ 74*K^4 := by
  have hzero : (0:FubiniBase) ∈ Metric.closedBall (0:FubiniBase) 1 := by simp
  exact FubiniQuadric.mass_quadric hK _ _ _ (data.rho_bound 0 hzero) (data.f_bound 0 hzero)
    (data.grad_bound 0 hzero) (data.H_bound 0 hzero) (data.m_bound 0 hzero) (data.lam_bound 0 hzero)

theorem radial_mem {x : FubiniBase} (hx : x ∈ Metric.closedBall (0:FubiniBase) 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : t • x ∈ Metric.closedBall (0:FubiniBase) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hxn : ‖x‖ ≤ 1 := by simpa using hx
  exact (mul_le_mul_of_nonneg_left hxn ht.1).trans (by simpa using ht.2)

/-- All radial frame variables of an actual graph satisfy the scalar
cancellation identities used to freeze its quadric. -/
theorem frozen_graph_estimates (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
    |eval (Fin.snoc (fun i => x i) (data.f x)) data.frozen| ≤ 1000*K^3*ε ∧
    |eval (Fin.snoc (fun i => x i) (data.f x)) (pderiv (3:Fin 4) data.frozen)-2*data.rho x| ≤
      1000*K^3*ε := by
  let d : ℝ → Fin 3 → ℝ := fun t i => (1-t)*x i
  let k : ℝ → ℝ := fun t => data.f x-data.f (t • x)-∑ i : Fin 3, data.grad (t • x) i*d t i
  let B : ℝ → ℝ := fun t => ∑ i : Fin 3, ∑ j : Fin 3, d t i*data.H (t • x) i j*d t j
  let n : ℝ → ℝ := fun t => ∑ i : Fin 3, data.m (t • x) i*d t i
  let mv : ℝ → ℝ := fun t => ∑ i : Fin 3, data.m (t • x) i*x i
  let v : ℝ → ℝ := fun t => ∑ i : Fin 3, ∑ j : Fin 3, x i*data.H (t • x) i j*d t j
  let Ec : ℝ → ℝ := fun t => ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    data.E (t • x) l i j*x l*d t i*d t j
  let Tc : ℝ → ℝ := fun t => ∑ l : Fin 3, ∑ i : Fin 3, data.T (t • x) l i*x l*d t i
  let Wc : ℝ → ℝ := fun t => ∑ l : Fin 3, data.W (t • x) l*x l
  have hd (t : ℝ) (i : Fin 3) : HasDerivAt (fun s => d s i) (-x i) t := by
    convert ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (x i) using 1 <;> simp [d]
  have hk : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt k (-v t) t := by
    intro t ht
    have hh := ((hasDerivAt_const t (data.f x)).sub (data.f_deriv x hx t ht)).sub
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (data.grad_deriv x hx t ht i).mul (hd t i)))
    convert hh using 1
    dsimp only [v, d]
    simp only [Fin.sum_univ_three]
    ring
  have hB : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt B (mv t*B t+2*n t*v t+Ec t-2*v t) t := by
    intro t ht
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hd t i).mul (data.H_deriv x hx t ht i j)).mul (hd t j))))
    convert hh using 1
    dsimp only [mv, B, n, v, Ec, d]
    simp only [fubiniCubic, Fin.sum_univ_three, Pi.mul_apply]
    ring
  have hn : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt n (mv t*n t+data.lam (t • x)*v t+Tc t-mv t) t := by
    intro t ht
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (data.m_deriv x hx t ht i).mul (hd t i))
    convert hh using 1
    dsimp only [mv, n, v, Tc]
    simp only [Fin.sum_univ_three]
    ring
  have hlam : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => data.lam (s • x)) (data.lam (t • x)*mv t+Wc t) t := by
    intro t ht
    convert data.lam_deriv x hx t ht using 1
    dsimp only [mv, Wc]
    simp only [Fin.sum_univ_three]
    ring
  have hxcoord : ∀ i : Fin 3, |x i| ≤ 1 := fun i =>
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans
      (by simpa using hx)
  have hdcoord : ∀ t ∈ Icc (0:ℝ) 1, ∀ i : Fin 3, |d t i| ≤ 1 := by
    intro t ht i
    dsimp only [d]
    rw [abs_mul, abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-t)]
    exact (mul_le_mul_of_nonneg_left (hxcoord i) (by linarith [ht.2])).trans (by linarith [ht.1])
  have hkb : ∀ t ∈ Icc (0:ℝ) 1, |k t| ≤ 5*K := by
    intro t ht
    have hsum : |∑ i : Fin 3, data.grad (t • x) i*d t i| ≤ 3*K := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ _i : Fin 3, K := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact (mul_le_mul (data.grad_bound _ (radial_mem hx ht) i) (hdcoord t ht i)
            (abs_nonneg _) (by linarith)).trans_eq (mul_one K)
        _ = _ := by simp
    have hf1 := data.f_bound x hx
    have hf2 := data.f_bound (t • x) (radial_mem hx ht)
    dsimp only [k]
    have h1 := abs_sub (data.f x-data.f (t • x))
      (∑ i : Fin 3, data.grad (t • x) i*d t i)
    have h2 := abs_sub (data.f x) (data.f (t • x))
    linarith
  have hEb : ∀ t ∈ Icc (0:ℝ) 1, |Ec t| ≤ 27*ε := by
    intro t ht
    have hterm (l i j : Fin 3) : |data.E (t • x) l i j*x l*d t i*d t j| ≤ ε := by
      simp only [abs_mul]
      calc
        _ ≤ ε*1*1*1 := by
          gcongr
          · exact data.E_bound _ (radial_mem hx ht) l i j
          · exact hxcoord l
          · exact hdcoord t ht i
          · exact hdcoord t ht j
        _ = _ := by ring
    calc
      _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, |data.E (t • x) l i j*x l*d t i*d t j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ _l : Fin 3, ∑ _i : Fin 3, ∑ _j : Fin 3, ε :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm l i j
      _ = _ := by simp; ring
  have hTb : ∀ t ∈ Icc (0:ℝ) 1, |Tc t| ≤ 9*ε := by
    intro t ht
    calc
      _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, |data.T (t • x) l i*x l*d t i| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _l : Fin 3, ∑ _i : Fin 3, ε :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul]
          calc
            _ ≤ ε*1*1 := by
              gcongr
              · exact data.T_bound _ (radial_mem hx ht) l i
              · exact hxcoord l
              · exact hdcoord t ht i
            _ = _ := by ring
      _ = _ := by simp; ring
  have hWb : ∀ t ∈ Icc (0:ℝ) 1, |Wc t| ≤ 3*ε := by
    intro t ht
    calc
      _ ≤ ∑ l : Fin 3, |data.W (t • x) l*x l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin 3, ε := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact (mul_le_mul (data.W_bound _ (radial_mem hx ht) l) (hxcoord l) (abs_nonneg _) hε).trans_eq (mul_one ε)
      _ = _ := by simp
  have hfreeze := freeze_fubini_frame (fun t => data.rho (t • x)) k B n
    (fun t => data.lam (t • x)) mv v Ec Tc Wc hK hε
    (fun t ht => data.rho_deriv x hx t ht) hk hB hn hlam
    (fun t ht => data.rho_bound _ (radial_mem hx ht)) hkb hEb hTb hWb
  constructor
  · have hh := hfreeze.1
    simpa only [k, B, n, d, one_smul, zero_smul, sub_self, zero_mul, mul_zero,
      Finset.sum_const_zero, sub_zero, pow_two, fubiniFrameValue, FubiniGraphData.frozen,
      FubiniQuadric.eval_quadric, zero_sub, one_mul, abs_neg] using hh
  · have hh := hfreeze.2
    rw [abs_sub_comm] at hh
    simpa only [k, B, n, d, one_smul, zero_smul, sub_self, zero_mul, mul_zero,
      Finset.sum_const_zero, sub_zero, fubiniFrameVertical, FubiniGraphData.frozen,
      FubiniQuadric.eval_pderiv_quadric, one_mul, mul_comm] using hh


/-- A regular frame produces a quantitatively regular quadratic graph
certificate, with error linear in the Fubini defects. -/
theorem frozen_graph_certificate (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hsmall : 1000*K^4*ε ≤ 1)
    (hrho : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, K⁻¹ ≤ data.rho x) :
    data.frozen.totalDegree ≤ 2 ∧
    (∀ e, |data.frozen.coeff e| ≤ 74*K^4) ∧
    ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      |eval (Fin.snoc (fun i => x i) (data.f x)) data.frozen| ≤ 1000*K^3*ε ∧
      K⁻¹ ≤ eval (Fin.snoc (fun i => x i) (data.f x)) (pderiv (3:Fin 4) data.frozen) ∧
      eval (Fin.snoc (fun i => x i) (data.f x)) (pderiv (3:Fin 4) data.frozen) ≤ 3*K ∧
      |eval (Fin.snoc (fun i => x i) (data.f x))
        (pderiv (3:Fin 4) (pderiv (3:Fin 4) data.frozen))| ≤ 2*K^2 := by
  have hK0 : 0 < K := by linarith
  have herr : 1000*K^3*ε ≤ K⁻¹ := by
    rw [← one_div, le_div_iff₀ hK0]
    convert hsmall using 1 <;> ring
  have hinv : K⁻¹ ≤ K := by
    have hh : K⁻¹ ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hK
    exact hh.trans hK
  refine ⟨data.frozen_degree, ?_, ?_⟩
  · intro e
    exact (Submission.Lib.K4ChartLifting.abs_coeff_le_coeffL1 _ _).trans (data.frozen_mass hK)
  · intro x hx
    obtain ⟨hval, hder⟩ := data.frozen_graph_estimates hK hε x hx
    have hlo := hrho x hx
    have hhi : data.rho x ≤ K := (le_abs_self _).trans (data.rho_bound x hx)
    refine ⟨hval, ?_, ?_, ?_⟩
    · linarith [(abs_le.mp hder).1]
    · linarith [(abs_le.mp hder).2]
    · rw [frozen, FubiniQuadric.pderiv_twice_quadric, eval_C]
      have hzero : (0:FubiniBase) ∈ Metric.closedBall (0:FubiniBase) 1 := by simp
      rw [abs_mul, abs_mul, abs_neg]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc
        _ ≤ 2*K*K := by gcongr; exact data.rho_bound 0 hzero; exact data.lam_bound 0 hzero
        _ = _ := by ring

end FubiniGraphData

end

end Submission.Obl.k4_physical_parent_potential_candidates
