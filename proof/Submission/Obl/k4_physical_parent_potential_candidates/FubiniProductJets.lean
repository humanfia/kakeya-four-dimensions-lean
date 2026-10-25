import Submission.Obl.k4_physical_parent_potential_candidates.FubiniJets

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set Filter FubiniJets

noncomputable section

namespace FubiniProductJets

/-- Equality on an open neighbourhood gives equality of actual coordinate jets. -/
theorem jet_eq_of_eqOn {f g : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (heq : EqOn f g U) {x : FubiniBase} (hx : x ∈ U)
    (n : ℕ) (α : Fin n → Fin 3) : jet f n α x = jet g n α x := by
  have he : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq
  exact congrArg (fun T => T (fun i => basis (α i))) (he.iteratedFDeriv ℝ n).eq_of_nhds

theorem jet_add {f g : FubiniBase → ℝ} {U : Set FubiniBase} {N : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    {x : FubiniBase} (hx : x ∈ U) (n : ℕ) (hn : (n:WithTop ℕ∞) ≤ N)
    (α : Fin n → Fin 3) :
    jet (fun y => f y+g y) n α x = jet f n α x+jet g n α x := by
  change (iteratedFDeriv ℝ n (f+g) x) _ = _
  rw [iteratedFDeriv_add_apply ((hf.of_le hn).contDiffAt (hU.mem_nhds hx))
    ((hg.of_le hn).contDiffAt (hU.mem_nhds hx))]
  rfl

theorem jet_const_mul {f : FubiniBase → ℝ} {U : Set FubiniBase} {N : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {x : FubiniBase} (hx : x ∈ U)
    (r : ℝ) (n : ℕ) (hn : (n:WithTop ℕ∞) ≤ N) (α : Fin n → Fin 3) :
    jet (fun y => r*f y) n α x = r*jet f n α x := by
  change (iteratedFDeriv ℝ n (r • f) x) _ = _
  rw [iteratedFDeriv_const_smul_apply ((hf.of_le hn).contDiffAt (hU.mem_nhds hx))]
  rfl

/-- First coordinate derivative of a product. -/
theorem first_mul {f g : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    {x : FubiniBase} (hx : x ∈ U) (i : Fin 3) :
    jet (fun y => f y*g y) 1 ![i] x = jet f 1 ![i] x*g x+f x*jet g 1 ![i] x := by
  have hh := (hasDerivAt_coordinate_value hU hf (by norm_num) x hx i).mul
    (hasDerivAt_coordinate_value hU hg (by norm_num) x hx i)
  simp only [zero_smul, add_zero] at hh
  exact (hasDerivAt_coordinate_value hU (hf.mul hg) (by norm_num) x hx i).unique hh

/-- Second coordinate derivative of a product. -/
theorem second_mul {f g : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    {x : FubiniBase} (hx : x ∈ U) (i j : Fin 3) :
    jet (fun y => f y*g y) 2 ![i,j] x =
      jet f 2 ![i,j] x*g x+jet f 1 ![j] x*jet g 1 ![i] x+
      jet f 1 ![i] x*jet g 1 ![j] x+f x*jet g 2 ![i,j] x := by
  have hh := ((hasDerivAt_coordinate_jet hU hf (by norm_num) ![j] x hx i).mul
      (hasDerivAt_coordinate_value hU hg (by norm_num) x hx i)).add
    ((hasDerivAt_coordinate_value hU hf (by norm_num) x hx i).mul
      (hasDerivAt_coordinate_jet hU hg (by norm_num) ![j] x hx i))
  simp only [zero_smul, add_zero] at hh
  have hc : ContinuousAt (fun s : ℝ => x+s • basis i) 0 := by fun_prop
  have hnear : ∀ᶠ s in nhds (0:ℝ), x+s • basis i ∈ U := by
    apply hc.eventually
    simpa using hU.mem_nhds hx
  have he : (fun s : ℝ => jet (fun y => f y*g y) 1 ![j] (x+s • basis i)) =ᶠ[nhds (0:ℝ)]
      (fun s => jet f 1 ![j] (x+s • basis i)*g (x+s • basis i)+
        f (x+s • basis i)*jet g 1 ![j] (x+s • basis i)) := by
    filter_upwards [hnear] with s hs
    exact first_mul hU hf hg hs j
  have hd := hh.congr_of_eventuallyEq he
  have huniq := (hasDerivAt_coordinate_jet hU (hf.mul hg) (by norm_num) ![j] x hx i).unique hd
  change jet (fun y => f y*g y) 2 ![i,j] x = _ at huniq
  convert huniq using 1
  change _ = (jet f 2 ![i,j] x*g x+jet f 1 ![j] x*jet g 1 ![i] x)+
    (jet f 1 ![i] x*jet g 1 ![j] x+f x*jet g 2 ![i,j] x)
  ring

/-- Third coordinate derivative of a product, retaining the eight Leibniz
terms so quadratic implicit equations can be differentiated exactly. -/
theorem third_mul {f g : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 3 f U) (hg : ContDiffOn ℝ 3 g U)
    {x : FubiniBase} (hx : x ∈ U) (i j k : Fin 3) :
    jet (fun y => f y*g y) 3 ![i,j,k] x =
      jet f 3 ![i,j,k] x*g x+jet f 2 ![j,k] x*jet g 1 ![i] x+
      jet f 2 ![i,k] x*jet g 1 ![j] x+jet f 1 ![k] x*jet g 2 ![i,j] x+
      jet f 2 ![i,j] x*jet g 1 ![k] x+jet f 1 ![j] x*jet g 2 ![i,k] x+
      jet f 1 ![i] x*jet g 2 ![j,k] x+f x*jet g 3 ![i,j,k] x := by
  have h1 := (hasDerivAt_coordinate_jet hU hf (by norm_num) ![j,k] x hx i).mul
    (hasDerivAt_coordinate_value hU hg (by norm_num) x hx i)
  have h2 := (hasDerivAt_coordinate_jet hU hf (by norm_num) ![k] x hx i).mul
    (hasDerivAt_coordinate_jet hU hg (by norm_num) ![j] x hx i)
  have h3 := (hasDerivAt_coordinate_jet hU hf (by norm_num) ![j] x hx i).mul
    (hasDerivAt_coordinate_jet hU hg (by norm_num) ![k] x hx i)
  have h4 := (hasDerivAt_coordinate_value hU hf (by norm_num) x hx i).mul
    (hasDerivAt_coordinate_jet hU hg (by norm_num) ![j,k] x hx i)
  have hh' := ((h1.add h2).add h3).add h4
  simp only [zero_smul, add_zero] at hh'
  have hc : ContinuousAt (fun s : ℝ => x+s • basis i) 0 := by fun_prop
  have hnear : ∀ᶠ s in nhds (0:ℝ), x+s • basis i ∈ U := by
    apply hc.eventually
    simpa using hU.mem_nhds hx
  have he : (fun s : ℝ => jet (fun y => f y*g y) 2 ![j,k] (x+s • basis i)) =ᶠ[nhds (0:ℝ)]
      (fun s => jet f 2 ![j,k] (x+s • basis i)*g (x+s • basis i)+
        jet f 1 ![k] (x+s • basis i)*jet g 1 ![j] (x+s • basis i)+
        jet f 1 ![j] (x+s • basis i)*jet g 1 ![k] (x+s • basis i)+
        f (x+s • basis i)*jet g 2 ![j,k] (x+s • basis i)) := by
    filter_upwards [hnear] with s hs
    exact second_mul hU (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hs j k
  have hd := hh'.congr_of_eventuallyEq he
  have huniq := (hasDerivAt_coordinate_jet hU (hf.mul hg) (by norm_num) ![j,k] x hx i).unique hd
  change jet (fun y => f y*g y) 3 ![i,j,k] x = _ at huniq
  convert huniq using 1
  change _ = (((jet f 3 ![i,j,k] x*g x+jet f 2 ![j,k] x*jet g 1 ![i] x)+
    (jet f 2 ![i,k] x*jet g 1 ![j] x+jet f 1 ![k] x*jet g 2 ![i,j] x))+
    (jet f 2 ![i,j] x*jet g 1 ![k] x+jet f 1 ![j] x*jet g 2 ![i,k] x))+
    (jet f 1 ![i] x*jet g 2 ![j,k] x+f x*jet g 3 ![i,j,k] x)
  ring

private theorem cancel_product {K d e M : ℝ} (hK : 0 < K) (hd : K⁻¹ ≤ |d|)
    (hm : |d*e| ≤ M) : |e| ≤ K*M := by
  have h1 : 1 ≤ K*|d| := by
    simpa only [mul_inv_cancel₀ hK.ne'] using mul_le_mul_of_nonneg_left hd hK.le
  calc
    |e| = 1*|e| := (one_mul _).symm
    _ ≤ (K*|d|)*|e| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = K*|d*e| := by rw [abs_mul]; ring
    _ ≤ K*M := mul_le_mul_of_nonneg_left hm hK.le

/-- Dividing a C²-small numerator by a regular C² denominator preserves
linear accuracy. The derivatives here are actual coordinate jets. -/
theorem small_of_product
    {n d e : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hd : ContDiffOn ℝ 2 d U) (he : ContDiffOn ℝ 2 e U)
    (hprod : ∀ y ∈ U, n y = d y*e y)
    {x : FubiniBase} (hx : x ∈ U) {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hreg : K⁻¹ ≤ |d x|)
    (hD1 : ∀ i, |jet d 1 ![i] x| ≤ K) (hD2 : ∀ i j, |jet d 2 ![i,j] x| ≤ K)
    (hN0 : |n x| ≤ ε) (hN1 : ∀ i, |jet n 1 ![i] x| ≤ ε)
    (hN2 : ∀ i j, |jet n 2 ![i,j] x| ≤ ε) :
    |e x| ≤ K*ε ∧ (∀ i, |jet e 1 ![i] x| ≤ 2*K^3*ε) ∧
      ∀ i j, |jet e 2 ![i,j] x| ≤ 6*K^5*ε := by
  have hK0 : 0 < K := by linarith
  have hK13 : K ≤ K^3 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
  have hK24 : K^2 ≤ K^4 := pow_le_pow_right₀ hK (by decide : 2 ≤ 4)
  have hK04 : 1 ≤ K^4 := one_le_pow₀ hK
  have hE0 : |e x| ≤ K*ε := cancel_product hK0 hreg (by simpa only [← hprod x hx] using hN0)
  have hfirst (i : Fin 3) : jet n 1 ![i] x = jet d 1 ![i] x*e x+d x*jet e 1 ![i] x := by
    rw [jet_eq_of_eqOn hU hprod hx, first_mul hU hd he hx]
  have hE1 (i : Fin 3) : |jet e 1 ![i] x| ≤ 2*K^3*ε := by
    have hpe : |jet d 1 ![i] x*e x| ≤ K*(K*ε) := by
      rw [abs_mul]
      exact mul_le_mul (hD1 i) hE0 (abs_nonneg _) hK0.le
    have hmul : |d x*jet e 1 ![i] x| ≤ ε+K*(K*ε) := by
      rw [show d x*jet e 1 ![i] x = jet n 1 ![i] x-jet d 1 ![i] x*e x by linarith [hfirst i]]
      exact (abs_sub _ _).trans (add_le_add (hN1 i) hpe)
    apply (cancel_product hK0 hreg hmul).trans
    have hh := mul_le_mul_of_nonneg_right hK13 hε
    nlinarith
  have hsecond (i j : Fin 3) : jet n 2 ![i,j] x =
      jet d 2 ![i,j] x*e x+jet d 1 ![j] x*jet e 1 ![i] x+
      jet d 1 ![i] x*jet e 1 ![j] x+d x*jet e 2 ![i,j] x := by
    rw [jet_eq_of_eqOn hU hprod hx, second_mul hU hd he hx]
  refine ⟨hE0, hE1, ?_⟩
  intro i j
  have ht0 : |jet d 2 ![i,j] x*e x| ≤ K^2*ε := by
    rw [abs_mul]
    convert mul_le_mul (hD2 i j) hE0 (abs_nonneg _) hK0.le using 1 <;> ring
  have ht1 (i j : Fin 3) : |jet d 1 ![i] x*jet e 1 ![j] x| ≤ 2*K^4*ε := by
    rw [abs_mul]
    convert mul_le_mul (hD1 i) (hE1 j) (abs_nonneg _) hK0.le using 1 <;> ring
  have hmul : |d x*jet e 2 ![i,j] x| ≤ ε+K^2*ε+4*K^4*ε := by
    rw [show d x*jet e 2 ![i,j] x = jet n 2 ![i,j] x-
      (jet d 2 ![i,j] x*e x+jet d 1 ![j] x*jet e 1 ![i] x+
        jet d 1 ![i] x*jet e 1 ![j] x) by linarith [hsecond i j]]
    have hh := abs_sub (jet n 2 ![i,j] x)
      (jet d 2 ![i,j] x*e x+jet d 1 ![j] x*jet e 1 ![i] x+
        jet d 1 ![i] x*jet e 1 ![j] x)
    linarith [abs_add_le (jet d 2 ![i,j] x*e x) (jet d 1 ![j] x*jet e 1 ![i] x),
      abs_add_le (jet d 2 ![i,j] x*e x+jet d 1 ![j] x*jet e 1 ![i] x)
        (jet d 1 ![i] x*jet e 1 ![j] x), hN2 i j, ht1 i j, ht1 j i]
  apply (cancel_product hK0 hreg hmul).trans
  have h1 := mul_le_mul_of_nonneg_right hK04 hε
  have h2 := mul_le_mul_of_nonneg_right hK24 hε
  nlinarith

end FubiniProductJets

end

end Submission.Obl.k4_physical_parent_potential_candidates
