/-
Adapted from: here:o116
Original proofs by session x0394, o116 branch x0394, commit be640a0.
Source: Submission/Obl/k4_isotropic_residual_candidates/ThirdBound.lean.
This helper has not entered lib.
-/
import Submission.Obl.k4_seven_direction_third_derivative_bound.IteratedSymm

/-!
# The third derivative from two-copy cubic tests

In the local degree restoration (o144) the hypotheses bound, for seven conditioned directions
`p_i`, the derivative of `v ↦ D²f(v)(p_i, p_i)`. With the symmetry of `D³f` these are the
two-copy tests `D³f(v)(p_i, p_i, e_j)`; the cubic two-copy kernel (x0001's
`TensorConditioningProp`, first conjunct, taken here as the hypothesis `TwoCopyCubicProp`) then
bounds every coordinate entry, hence the norm of `D³f(v)`.
-/

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Vec3
variable {α : Type*}
lemma vec3_update0 (a b c x : α) : Function.update ![a, b, c] 0 x = ![x, b, c] := by
  funext j; fin_cases j <;> rfl
lemma vec3_update1 (a b c x : α) : Function.update ![a, b, c] 1 x = ![a, x, c] := by
  funext j; fin_cases j <;> rfl
lemma vec3_update2 (a b c x : α) : Function.update ![a, b, c] 2 x = ![a, b, x] := by
  funext j; fin_cases j <;> rfl
end Vec3

section Tri
variable (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E3) ℝ)

lemma tri_add0 (a a' b c : E3) : M ![a + a', b, c] = M ![a, b, c] + M ![a', b, c] := by
  have h := M.map_update_add ![a, b, c] 0 a a'
  simpa only [vec3_update0] using h
lemma tri_add1 (a b b' c : E3) : M ![a, b + b', c] = M ![a, b, c] + M ![a, b', c] := by
  have h := M.map_update_add ![a, b, c] 1 b b'
  simpa only [vec3_update1] using h
lemma tri_add2 (a b c c' : E3) : M ![a, b, c + c'] = M ![a, b, c] + M ![a, b, c'] := by
  have h := M.map_update_add ![a, b, c] 2 c c'
  simpa only [vec3_update2] using h
lemma tri_smul0 (r : ℝ) (a b c : E3) : M ![r • a, b, c] = r * M ![a, b, c] := by
  have h := M.map_update_smul ![a, b, c] 0 r a
  simpa only [vec3_update0, smul_eq_mul] using h
lemma tri_smul1 (r : ℝ) (a b c : E3) : M ![a, r • b, c] = r * M ![a, b, c] := by
  have h := M.map_update_smul ![a, b, c] 1 r b
  simpa only [vec3_update1, smul_eq_mul] using h
lemma tri_smul2 (r : ℝ) (a b c : E3) : M ![a, b, r • c] = r * M ![a, b, c] := by
  have h := M.map_update_smul ![a, b, c] 2 r c
  simpa only [vec3_update2, smul_eq_mul] using h
end Tri

/-- A trilinear form on `ℝ³` read in coordinates. -/
noncomputable def triCoord (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E3) ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => M ![WithLp.toLp 2 x, WithLp.toLp 2 y, WithLp.toLp 2 z]
          map_add' := fun z z' => by simp only [WithLp.toLp_add, tri_add2]
          map_smul' := fun r z => by simp only [WithLp.toLp_smul, tri_smul2, RingHom.id_apply,
            smul_eq_mul] }
      map_add' := fun y y' => by refine LinearMap.ext fun z => ?_; simp only [WithLp.toLp_add, tri_add1, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.add_apply]
      map_smul' := fun r y => by refine LinearMap.ext fun z => ?_; simp only [WithLp.toLp_smul, tri_smul1, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] }
  map_add' := fun x x' => by refine LinearMap.ext fun y => LinearMap.ext fun z => ?_; simp only [WithLp.toLp_add, tri_add0, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := fun r x => by refine LinearMap.ext fun y => LinearMap.ext fun z => ?_; simp only [WithLp.toLp_smul, tri_smul0, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]

lemma triCoord_apply (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E3) ℝ) (x y z : Fin 3 → ℝ) :
    triCoord M x y z = M ![WithLp.toLp 2 x, WithLp.toLp 2 y, WithLp.toLp 2 z] := rfl

/-- The derivative of a fixed diagonal evaluation of `D^n f` is `D^(n+1) f` with the new
direction in the first slot. -/
lemma fderiv_iteratedFDeriv_apply_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {f : E → F} {u : E}
    (hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) u) (m : Fin n → E) (e : E) :
    fderiv ℝ (fun v => iteratedFDeriv ℝ n f v m) u e =
      iteratedFDeriv ℝ (n + 1) f u (Fin.cons e m) := by
  have : (fun v => iteratedFDeriv ℝ n f v m) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F m) ∘ iteratedFDeriv ℝ n f := rfl
  rw [this, fderiv_comp u (ContinuousLinearMap.differentiableAt _) hdiff,
    ContinuousLinearMap.fderiv, iteratedFDeriv_succ_apply_left]
  simp

/-- A trilinear form on `ℝ³` whose coordinate entries are at most `M0` has norm at most `27 M0`. -/
lemma norm_le_of_coord (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E3) ℝ) {M0 : ℝ}
    (hM0 : 0 ≤ M0)
    (h : ∀ a b c : Fin 3, |triCoord M (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)| ≤ M0) :
    ‖M‖ ≤ 27 * M0 := by
  classical
  refine M.opNorm_le_bound (by positivity) fun m => ?_
  have hexp : m = fun i => ∑ a, m i a • EuclideanSpace.single a (1 : ℝ) := by
    funext i
    ext j
    simp [Pi.single_apply]
  have hMm : M m = ∑ r : Fin 3 → Fin 3,
      M (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ)) := by
    conv_lhs => rw [hexp]
    exact M.map_sum (fun i a => m i a • EuclideanSpace.single a (1 : ℝ))
  rw [hMm]
  have hterm : ∀ r : Fin 3 → Fin 3,
      ‖M (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ))‖ ≤ M0 * ∏ i, ‖m i‖ := by
    intro r
    rw [M.map_smul_univ, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
    have hT : |M (fun i => EuclideanSpace.single (r i) (1 : ℝ))| ≤ M0 := by
      have := h (r 0) (r 1) (r 2)
      rw [triCoord_apply] at this
      convert this using 3
      funext i
      fin_cases i <;> rfl
    calc (∏ i, |m i (r i)|) * |M (fun i => EuclideanSpace.single (r i) (1 : ℝ))|
        ≤ (∏ i, ‖m i‖) * M0 := mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            (fun i _ => (by simpa only [Real.norm_eq_abs] using
              PiLp.norm_apply_le (m i) (r i)))) hT (abs_nonneg _)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = M0 * ∏ i, ‖m i‖ := mul_comm _ _
  calc ‖∑ r : Fin 3 → Fin 3, M (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ))‖
      ≤ ∑ r : Fin 3 → Fin 3, ‖M (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r : Fin 3 → Fin 3, M0 * ∏ i, ‖m i‖ := Finset.sum_le_sum fun r _ => hterm r
    _ = 27 * M0 * ∏ i, ‖m i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

/-- The cubic two-copy kernel of x0001's `TensorConditioningProp` (first conjunct), as a
standalone hypothesis shape. -/
def TwoCopyCubicProp : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ (A ε : ℝ), 2 ≤ A → 0 ≤ ε →
    ∀ p : Fin 7 → Fin 3 → ℝ,
      (∀ i j, |p i j| ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|) →
      ∀ T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
        (∀ x y z, T x y z = T y x z) → (∀ x y z, T x y z = T x z y) →
        (∀ i : Fin 7, ∀ j : Fin 3, |T (p i) (p i) (Pi.single j 1)| ≤ ε) →
        ∀ i j k : Fin 3, |T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)| ≤ A ^ C * ε

/-- **Third derivative from two-copy tests.** At a point of an open set where `f` is `C^3`,
bounds `B` on the derivatives of the seven second directional derivatives `D²f(·)(p_i,p_i)`
bound the whole third derivative by `A^K B`. -/
theorem norm_third_le_of_two_copy (hTC : TwoCopyCubicProp) :
    ∃ K : ℕ, ∀ (A B : ℝ) (f : E3 → ℝ) (p : Fin 7 → E3) (U : Set E3), 2 ≤ A → 0 ≤ B →
      IsOpen U → ContDiffOn ℝ 3 f U → (∀ i, ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      ∀ u ∈ U, (∀ i : Fin 7,
        ‖iteratedFDeriv ℝ 1 (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ ≤ B) →
        ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ K * B := by
  obtain ⟨C, -, hC⟩ := hTC
  refine ⟨C + 5, ?_⟩
  intro A B f p U hA hB hU hf hp hdet u hu htest
  have hA0 : 0 < A := by linarith
  set M := iteratedFDeriv ℝ 3 f u with hMdef
  -- symmetry of `M`
  have hsymm : ∀ (v : Fin 3 → E3) (σ : Equiv.Perm (Fin 3)), M (v ∘ σ) = M v :=
    fun v σ => iteratedFDeriv_comp_perm_of_contDiffOn hU hf hu v σ
  set p' : Fin 7 → Fin 3 → ℝ := fun i j => p i j with hp'
  have hp'b : ∀ i j, |p' i j| ≤ A := fun i j => (show |p i j| ≤ ‖p i‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p i) j).trans (hp i)
  have hdet' : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p' i, p' j, p' k])| := by
    intro i j k hij hik hjk
    have h := hdet i j k hij hik hjk
    convert h using 3
    ext r t
    fin_cases r <;> rfl
  set T := triCoord M
  have hT01 : ∀ x y z, T x y z = T y x z := by
    intro x y z
    simp only [T, triCoord_apply]
    rw [← hsymm _ (Equiv.swap 0 1)]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hT12 : ∀ x y z, T x y z = T x z y := by
    intro x y z
    simp only [T, triCoord_apply]
    rw [← hsymm _ (Equiv.swap 1 2)]
    congr 1
    funext i
    fin_cases i <;> rfl
  -- the tests are the directional hypotheses
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) u :=
    (hf.contDiffAt (hU.mem_nhds hu)).differentiableAt_iteratedFDeriv (by norm_num)
  have htests : ∀ i : Fin 7, ∀ j : Fin 3, |T (p' i) (p' i) (Pi.single j 1)| ≤ B := by
    intro i j
    have hpi : WithLp.toLp 2 (p' i) = p i := rfl
    have hsingle : WithLp.toLp 2 (Pi.single j (1 : ℝ) : Fin 3 → ℝ) = EuclideanSpace.single j 1 := rfl
    have hval : T (p' i) (p' i) (Pi.single j 1) =
        fderiv ℝ (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u (EuclideanSpace.single j 1) := by
      rw [fderiv_iteratedFDeriv_apply_const hdiff, ← hMdef]
      simp only [T, triCoord_apply, hpi, hsingle]
      rw [← hsymm _ (Equiv.swap 0 2)]
      congr 1
      funext l
      fin_cases l <;> rfl
    rw [hval]
    calc |fderiv ℝ (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u (EuclideanSpace.single j 1)|
        ≤ ‖fderiv ℝ (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ *
            ‖(EuclideanSpace.single j (1 : ℝ))‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ := by
          rw [norm_iteratedFDeriv_one, EuclideanSpace.norm_single, norm_one, mul_one]
      _ ≤ B := htest i
  have hcoord := hC A B hA hB p' hp'b hdet' T hT01 hT12 htests
  have hnorm := norm_le_of_coord M (by positivity) hcoord
  calc ‖M‖ ≤ 27 * (A ^ C * B) := hnorm
    _ ≤ A ^ 5 * (A ^ C * B) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (27 : ℝ) ≤ 2 ^ 5 := by norm_num
          _ ≤ A ^ 5 := pow_le_pow_left₀ (by norm_num) hA 5
    _ = A ^ (C + 5) * B := by ring

end Submission.Obl.k4_seven_direction_third_derivative_bound
