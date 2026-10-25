import Submission.Lib.K4PolynomialRemezThree.Comparison

/-!
Adapted from: here:o114 (session x0383), SmallAnchor.lean and SmallBallNorm.lean.
The private affine substitution kernel is promoted from this tree's o028
Signs/Families, using only Mathlib. General contributions cannot import an
obligation module.

Uniform coefficient/value and sublevel comparison on the fixed real anchor
ball. These also support coefficient normalization in local preparation.
-/

namespace Submission.Lib.K4PolynomialRemezThree

open Set Metric MeasureTheory MvPolynomial
open scoped Pointwise

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
  simpa only [aeval_def, algebraMap_eq, Function.comp_def] using (eval_assoc f x p).symm

/-- A large real value in the small base ball controls small sublevels in
that same ball. The displayed threshold has fixed degree-dependent exponent. -/
theorem volume_small_anchor_sublevel_lt (P : MvPolynomial (Fin 3) ℝ) {D : ℕ}
    (hP : P.totalDegree ≤ D) {V τ : ℝ} (hV : 0 < V) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (a : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ ≤ 1/8)
    (hlarge : V ≤ |eval (fun i => a i) P|) :
    volume {b : EuclideanSpace ℝ (Fin 3) | ‖b‖ ≤ 1/8 ∧
      |eval (fun i => b i) P| ≤ (V/2) * (τ/(32*(D+1)))^(3*D)} < ENNReal.ofReal τ := by
  let q : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i => C (-1/8) + C (1/4) * X i
  let Q := aeval q P
  let g : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x => (1/4 : ℝ) • x + fun _ => -1/8
  let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x i => 4*(x i + 1/8)
  have hq (i : Fin 3) : (q i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply (totalDegree_mul _ _).trans
      simp
  have hQ : Q.totalDegree ≤ D :=
    (degree_aeval_linear_le P q hq).trans hP
  have heval (x : Fin 3 → ℝ) : eval x Q = eval (g x) P := by
    dsimp only [Q]
    rw [eval_aeval_real]
    apply congrArg (fun y : Fin 3 → ℝ => eval y P)
    funext i
    simp only [q, g, eval_add, eval_C, eval_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hg (x : Fin 3 → ℝ) : g (f x) = x := by
    ext i
    dsimp [g, f]
    ring
  have hbox (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ 1/8) : f x ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    constructor <;> intro i <;> dsimp [f]
    · linarith [(abs_le.mp (hx i)).1]
    · linarith [(abs_le.mp (hx i)).2]
  have habox : f (fun i => a i) ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    apply hbox
    intro i
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le a i).trans ha
  have halarge : V ≤ |eval (f (fun i => a i)) Q| := by rw [heval, hg]; exact hlarge
  let U : Set (Fin 3 → ℝ) := {x | x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
    |eval x Q| ≤ (V/2) * (τ/(32*(D+1)))^(3*D)}
  have hU : volume U < ENNReal.ofReal τ :=
    volume_sublevel_lt_from_real_anchor D Q hQ hτ hτ1 hV habox halarge
  let S : Set (EuclideanSpace ℝ (Fin 3)) := {b | ‖b‖ ≤ 1/8 ∧
    |eval (fun i => b i) P| ≤ (V/2) * (τ/(32*(D+1)))^(3*D)}
  have hS : MeasurableSet S := by
    change MeasurableSet ({b : EuclideanSpace ℝ (Fin 3) | ‖b‖ ≤ 1/8} ∩
      {b | |eval (fun i => b i) P| ≤ (V/2) * (τ/(32*(D+1)))^(3*D)})
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le ((continuous_eval P).comp (by fun_prop)).abs.measurable measurable_const)
  have hsub : WithLp.toLp 2 ⁻¹' S ⊆ g '' U := by
    intro x hx
    refine ⟨f x, ?_, hg x⟩
    refine ⟨hbox x (fun i => ?_), ?_⟩
    · have hh := (PiLp.norm_apply_le (WithLp.toLp 2 x) i).trans hx.1
      simpa only [Real.norm_eq_abs, PiLp.toLp_apply] using hh
    · rw [heval, hg]
      exact hx.2
  have hgvol : volume (g '' U) ≤ volume U := by
    have himage : g '' U = (fun x : Fin 3 → ℝ => x + (fun _ => -1/8)) '' ((1/4:ℝ) • U) := by
      simp only [g, ← image_smul, image_image]
    rw [himage, image_add_right, measure_preimage_add_right, Measure.addHaar_smul]
    norm_num
    calc
      _ ≤ 1 * volume U := by gcongr; norm_num
      _ = volume U := one_mul _
  calc
    volume S = volume (WithLp.toLp 2 ⁻¹' S) :=
      ((PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hS.nullMeasurableSet).symm
    _ ≤ volume (g '' U) := measure_mono hsub
    _ ≤ volume U := hgvol
    _ < ENNReal.ofReal τ := hU


/-- A bound on the small real anchor ball controls every coefficient. -/
theorem exists_coefficient_bound_on_small_ball (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1/8 →
        |eval (fun i => x i) P| ≤ E) →
      ∀ d, |P.coeff d| ≤ C * E := by
  obtain ⟨K, hK, hcoeff⟩ := exists_coefficient_bound_on_unit_cube 3 D
  obtain ⟨L, hL, hcomplex⟩ := exists_complex_bound_from_real_cube 3 D
  refine ⟨K * (L * 32^D), by positivity, ?_⟩
  intro P hP E hE hsmall d
  let q : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i => C (1/32) * X i
  let Q := aeval q P
  have hq (i : Fin 3) : (q i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp [q])
  have hQ : Q.totalDegree ≤ D :=
    (degree_aeval_linear_le P q hq).trans hP
  have hQbox (x : Fin 3 → ℝ) (hx : x ∈ Icc (0 : Fin 3 → ℝ) 1) : |eval x Q| ≤ E := by
    let y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => (1/32:ℝ) * x i)
    have hy : ‖y‖ ≤ 1/8 := by
      have hsum : ∑ i : Fin 3, ‖y i‖^2 ≤ ∑ _i : Fin 3, (1/32:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hlo : 0 ≤ x i := hx.1 i
        have hhi : x i ≤ 1 := hx.2 i
        simp only [y, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      rw [← EuclideanSpace.norm_sq_eq] at hsum
      norm_num at hsum
      nlinarith [norm_nonneg y]
    have hh := hsmall y hy
    dsimp only [Q]
    rw [eval_aeval_real]
    simpa only [q, eval_mul, eval_C, eval_X, y, PiLp.toLp_apply] using hh
  have heval (x : Fin 3 → ℝ) :
      eval₂ (algebraMap ℝ ℂ) (fun i => (32:ℂ) * x i) Q = (eval x P : ℂ) := by
    let φ : MvPolynomial (Fin 3) ℝ →+* ℂ :=
      eval₂Hom (algebraMap ℝ ℂ) (fun i => (32:ℂ) * x i)
    change φ (aeval q P) = _
    rw [map_aeval]
    have hc : φ.comp (algebraMap ℝ (MvPolynomial (Fin 3) ℝ)) = algebraMap ℝ ℂ := by
      ext t
      simp [φ]
    rw [hc]
    have hv : (fun i => φ (q i)) = fun i => (x i : ℂ) := by
      funext i
      simp [φ, q]
    rw [hv]
    exact (eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ) x P).symm
  have hPbox (x : Fin 3 → ℝ) (hx : x ∈ Icc (0 : Fin 3 → ℝ) 1) :
      |eval x P| ≤ L * 32^D * E := by
    have hz (i : Fin 3) : ‖(32:ℂ) * x i‖ ≤ 32 := by
      rw [norm_mul, Complex.norm_real]
      norm_num
      rw [abs_of_nonneg (hx.1 i)]
      have hi : x i ≤ 1 := hx.2 i
      linarith
    have hh := hcomplex Q hQ E hE hQbox 32 (by norm_num) _ hz
    rw [heval, Complex.norm_real] at hh
    exact hh
  have hh := hcoeff P hP (L * 32^D * E) (by positivity) hPbox d
  convert hh using 1 <;> ring

/-- A coefficient lower bound gives one large real value in the anchor ball. -/
theorem exists_large_value_on_small_ball (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ W : ℝ, 0 < W → (∃ d, W ≤ |P.coeff d|) →
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1/8 ∧
        W / C ≤ |eval (fun i => x i) P| := by
  obtain ⟨K, hK, hbound⟩ := exists_coefficient_bound_on_small_ball D
  refine ⟨2*K, by positivity, ?_⟩
  intro P hP W hW ⟨d, hd⟩
  by_contra hn
  push Not at hn
  have h := hbound P hP (W/(2*K)) (by positivity)
    (fun x hx => (hn x hx).le) d
  have hmul : K * (W/(2*K)) = W/2 := by field_simp
  rw [hmul] at h
  linarith

/-- A coefficient lower bound controls the small-ball sublevel volume with
fixed degree-dependent constants, without any coefficient upper bound. -/
theorem exists_coefficient_sublevel_bound_on_small_ball (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ W τ : ℝ, 0 < W → 0 < τ → τ ≤ 1 → (∃ d, W ≤ |P.coeff d|) →
      volume {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1/8 ∧
        |eval (fun i => x i) P| ≤ (W/C) * (τ/(32*(D+1)))^(3*D)} < ENNReal.ofReal τ := by
  obtain ⟨K, hK, hlarge⟩ := exists_large_value_on_small_ball D
  refine ⟨2*K, by positivity, ?_⟩
  intro P hP W τ hW hτ hτ1 hcoeff
  obtain ⟨a, ha, hval⟩ := hlarge P hP W hW hcoeff
  have hh := volume_small_anchor_sublevel_lt P hP (div_pos hW hK) hτ hτ1 a ha hval
  have heq : (W/K)/2 = W/(2*K) := by field_simp
  simpa only [heq] using hh

end Submission.Lib.K4PolynomialRemezThree
