/-
Adapted from: here:o062
Purpose: Shared scalar switching helper SwitchEndpoint.
Original owned source: x0511, commit 618d12a, Submission/Obl/k4_scalar_mesh_projection/SwitchEndpoint.lean.
-/

/-
Local LOT source: session x0511, branch x0511, commit 618d12a,
Submission/Obl/k4_scalar_mesh_projection/SwitchEndpoint.lean.
Reviewed and integrated by x0212 for o062.
-/

import Submission.Lib.K4ScalarSwitching.SwitchPathBounds
import Submission.Lib.K4ScalarSwitching.EndpointChange
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Lib.K4ScalarSwitching.Switching

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4PolynomialPotential
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-- The first two endpoint coordinates and the last active increment.
The two initial velocities supply the invertible base change. -/
noncomputable def endpointBaseEquiv (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun δ := ![δ 0 + δ 1 + δ 2, v 0 * δ 0 + v 1 * δ 1 + v 2 * δ 2, δ 2]
  invFun z := ![(v 1 * z 0 - z 1 + (v 2 - v 1) * z 2) / (v 1 - v 0),
    (z 1 - v 0 * z 0 + (v 0 - v 2) * z 2) / (v 1 - v 0), z 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring
  left_inv δ := by
    ext i
    fin_cases i <;> simp <;> field_simp [h] <;> ring
  right_inv z := by
    ext i
    fin_cases i <;> simp <;> field_simp [h] <;> ring

theorem endpointBaseEquiv_apply (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0)
    (δ : Fin 3 → ℝ) :
    endpointBaseEquiv v h δ =
      ![δ 0 + δ 1 + δ 2, v 0 * δ 0 + v 1 * δ 1 + v 2 * δ 2, δ 2] := rfl

theorem endpointBaseEquiv_det (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0) :
    LinearMap.det (endpointBaseEquiv v h : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) =
      v 1 - v 0 := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix'
      (endpointBaseEquiv v h : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) =
      !![1, 1, 1; v 0, v 1, v 2; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, endpointBaseEquiv]
  simp [hm, Matrix.det_fin_three]

noncomputable def inverseEndpointValues (v : Fin 3 → ℝ) :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  ![C ((v 1 - v 0)⁻¹) * (C (v 1) * X 0 - X 1 + C (v 2 - v 1) * X 2),
    C ((v 1 - v 0)⁻¹) * (X 1 - C (v 0) * X 0 + C (v 0 - v 2) * X 2), X 2]

noncomputable def endpointPullback (v : Fin 3 → ℝ) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  aeval (inverseEndpointValues v)

theorem eval_inverseEndpointValues (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0)
    (z : Fin 3 → ℝ) :
    (fun k => eval z (inverseEndpointValues v k)) = (endpointBaseEquiv v h).symm z := by
  ext k
  fin_cases k <;> simp [inverseEndpointValues, endpointBaseEquiv, div_eq_mul_inv, mul_comm]

theorem eval_endpointPullback (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0)
    (P : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    eval z (endpointPullback v P) = eval ((endpointBaseEquiv v h).symm z) P := by
  rw [endpointPullback, eval_substitution, eval_inverseEndpointValues v h]

theorem partial_inverseEndpointValues (v : Fin 3 → ℝ) (k : Fin 3) :
    pderiv 2 (inverseEndpointValues v k) =
      C ((![((v 2 - v 1) / (v 1 - v 0)),
        ((v 0 - v 2) / (v 1 - v 0)), 1] : Fin 3 → ℝ) k) := by
  fin_cases k <;>
    simp [inverseEndpointValues, pderiv_X, div_eq_mul_inv, mul_comm]

/-- Under the base-plus-kernel coordinate change, the kernel height
derivative times the base determinant is the full endpoint determinant. -/
theorem endpointPullback_derivative (v : Fin 3 → ℝ) (h : v 1 - v 0 ≠ 0)
    (P : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    (v 1 - v 0) * eval z (pderiv 2 (endpointPullback v P)) =
      Matrix.det !![1, 1, 1; v 0, v 1, v 2;
        eval ((endpointBaseEquiv v h).symm z) (pderiv 0 P),
        eval ((endpointBaseEquiv v h).symm z) (pderiv 1 P),
        eval ((endpointBaseEquiv v h).symm z) (pderiv 2 P)] := by
  rw [endpointPullback, partial_aeval]
  simp only [partial_inverseEndpointValues, map_sum, map_mul, eval_C,
    eval_substitution, eval_inverseEndpointValues v h]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three]
  field_simp [h]
  ring

theorem inverseEndpointValues_degree (v : Fin 3 → ℝ) (k : Fin 3) :
    (inverseEndpointValues v k).totalDegree ≤ 1 := by
  fin_cases k <;> dsimp only [inverseEndpointValues]
  · apply (degree_C_mul_le _ _).trans
    apply degree_add_le
    · apply degree_sub_le
      · exact (degree_C_mul_le _ _).trans (by simp)
      · simp
    · exact (degree_C_mul_le _ _).trans (by simp)
  · apply (degree_C_mul_le _ _).trans
    apply degree_add_le
    · apply degree_sub_le
      · simp
      · exact (degree_C_mul_le _ _).trans (by simp)
    · exact (degree_C_mul_le _ _).trans (by simp)
  · simp

theorem endpointPullback_degree (v : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (endpointPullback v P).totalDegree ≤ P.totalDegree :=
  degree_aeval_le P (inverseEndpointValues v) (inverseEndpointValues_degree v)

noncomputable def endpointFiberPolynomial (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (x : Fin 2 → ℝ) : Polynomial ℝ :=
  coordinatePolynomialHom (![x 0, x 1, 0] : Fin 3 → ℝ) 2 (endpointPullback v P)

theorem eval_endpointFiberPolynomial (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (x : Fin 2 → ℝ) (s : ℝ) :
    (endpointFiberPolynomial v P x).eval s = eval (![x 0, x 1, s]) (endpointPullback v P) := by
  rw [endpointFiberPolynomial, eval_coordinatePolynomialHom]
  apply congrArg (fun z : Fin 3 → ℝ => eval z (endpointPullback v P))
  ext k
  fin_cases k <;> simp

theorem derivative_endpointFiberPolynomial (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (x : Fin 2 → ℝ) (s : ℝ) :
    (endpointFiberPolynomial v P x).derivative.eval s =
      eval (![x 0, x 1, s]) (pderiv 2 (endpointPullback v P)) := by
  rw [endpointFiberPolynomial, derivative_coordinatePolynomialHom,
    eval_coordinatePolynomialHom]
  apply congrArg (fun z : Fin 3 → ℝ => eval z (pderiv 2 (endpointPullback v P)))
  ext k
  fin_cases k <;> simp

theorem endpointFiberPolynomial_degree (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 3) ℝ) (x : Fin 2 → ℝ) :
    (endpointFiberPolynomial v P x).natDegree ≤ P.totalDegree := by
  apply Nat.le_trans _ (endpointPullback_degree v P)
  change (MvPolynomial.aeval
    (fun k => if k = (2 : Fin 3) then Polynomial.X else Polynomial.C ((![x 0, x 1, 0]) k))
      (endpointPullback v P)).natDegree ≤ (endpointPullback v P).totalDegree
  simpa only [Nat.mul_one] using
    MvPolynomial.aeval_natDegree_le (n := 1) (endpointPullback v P) le_rfl
      (fun k : Fin 3 => if k = 2 then Polynomial.X else Polynomial.C ((![x 0, x 1, 0]) k))
      (fun k => by split_ifs <;> simp)

/-- A scalar polynomial endpoint with two linear base coordinates satisfies
the base-area times height-width bound away from its actual Jacobian zero
set. No normalization or coefficient bound is imposed on the endpoint set. -/
theorem polynomial_endpoint_cells_volume_le {ι : Type*}
    (v : Fin 3 → ℝ) (hv : v 1 - v 0 ≠ 0) (P : MvPolynomial (Fin 3) ℝ)
    (D : ℕ) (hP : P.totalDegree ≤ D) (S : Set (Fin 3 → ℝ))
    (F : Finset ι) (E : ι → Set (Fin 2 → ℝ)) (c : ι → ℝ)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (hcover : ∀ δ ∈ S, ∃ i ∈ F,
      (![δ 0 + δ 1 + δ 2, v 0 * δ 0 + v 1 * δ 1 + v 2 * δ 2]) ∈ E i ∧
        |eval δ P - c i| ≤ ε)
    (hjac : ∀ δ ∈ S, κ ≤ |Matrix.det !![1, 1, 1; v 0, v 1, v 2;
      eval δ (pderiv 0 P), eval δ (pderiv 1 P), eval δ (pderiv 2 P)]|) :
    volume S ≤ (∑ i ∈ F, volume (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  let L := endpointBaseEquiv v hv
  have hreconstruct (z : Fin 3 → ℝ) : ![z 0, z 1, z 2] = z := by
    ext k
    fin_cases k <;> rfl
  have heval (z : Fin 3 → ℝ) :
      (endpointFiberPolynomial v P (scalarEndpointSplit z).1).eval
        (scalarEndpointSplit z).2 = eval (L.symm z) P := by
    simp only [scalarEndpointSplit_apply, eval_endpointFiberPolynomial,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hreconstruct, eval_endpointPullback]
  have hderiv (z : Fin 3 → ℝ) :
      (endpointFiberPolynomial v P (scalarEndpointSplit z).1).derivative.eval
        (scalarEndpointSplit z).2 = eval z (pderiv 2 (endpointPullback v P)) := by
    simp only [scalarEndpointSplit_apply, derivative_endpointFiberPolynomial,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hreconstruct]
  apply scalar_linear_endpoint_cells_volume_le L
    (by simpa only [L, endpointBaseEquiv_det] using hv)
    (endpointFiberPolynomial v P) S F E c D hε hκ hS hE
  · have hcont : Continuous (fun z : (Fin 2 → ℝ) × ℝ =>
        eval (![z.1 0, z.1 1, z.2]) (endpointPullback v P)) :=
      (MvPolynomial.continuous_eval _).comp (by fun_prop)
    simpa only [eval_endpointFiberPolynomial] using hcont.measurable
  · intro x
    exact (endpointFiberPolynomial_degree v P x).trans hP
  · intro δ hδ
    obtain ⟨i, hi, hb, hh⟩ := hcover δ hδ
    refine ⟨i, hi, ?_, ?_⟩
    · simpa only [L, scalarEndpointSplit_apply, endpointBaseEquiv_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] using hb
    · simpa only [heval, LinearEquiv.symm_apply_apply] using hh
  · intro δ hδ
    rw [hderiv, show LinearMap.det (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) =
      v 1 - v 0 from endpointBaseEquiv_det v hv, ← abs_mul,
      endpointPullback_derivative v hv, LinearEquiv.symm_apply_apply]
    exact hjac δ hδ

/-- Freezing one complementary increment gives the endpoint volume bound
with exactly the maximal minor detected by the four-leg curl identity. -/
theorem sliced_endpoint_cells_volume_le {ι : Type*}
    (v : Fin 4 → ℝ) (hv : v 1 - v 0 ≠ 0) (R : MvPolynomial (Fin 4) ℝ)
    (last : Fin 2) (w : ℝ) (D : ℕ) (hR : R.totalDegree ≤ D)
    (S : Set (Fin 3 → ℝ)) (F : Finset ι) (E : ι → Set (Fin 2 → ℝ)) (c : ι → ℝ)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (hcover : ∀ δ ∈ S, ∃ i ∈ F,
      (![δ 0 + δ 1 + δ 2, v 0 * δ 0 + v 1 * δ 1 + v (Fin.natAdd 2 last) * δ 2]) ∈ E i ∧
        |eval (slicePoint last w δ) R - c i| ≤ ε)
    (hjac : ∀ δ ∈ S, κ ≤
      |eval (slicePoint last w δ) (endpointMinor R v (Fin.natAdd 2 last))|) :
    volume S ≤ (∑ i ∈ F, volume (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  apply polynomial_endpoint_cells_volume_le
    (![v 0, v 1, v (Fin.natAdd 2 last)]) hv (endpointSlice last w R) D
    ((endpointSlice_degree R last w).trans hR) S F E c hε hκ hS hE
  · simpa [eval_endpointSlice] using hcover
  · intro δ hδ
    have h := hjac δ hδ
    rw [← eval_endpointSlice, slice_endpoint_jacobian] at h
    simpa using h

def complementaryControl (last : Fin 2) : Fin 4 := Fin.natAdd 2 last.rev

def switchingSplit (last : Fin 2) : (Fin 4 → ℝ) ≃ᵐ (ℝ × (Fin 3 → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (complementaryControl last)

theorem switchingSplit_symm_apply (last : Fin 2) (w : ℝ) (δ : Fin 3 → ℝ) :
    (switchingSplit last).symm (w, δ) = slicePoint last w δ := by
  ext k
  fin_cases last <;> fin_cases k <;> rfl

theorem volume_preserving_switchingSplit (last : Fin 2) :
    MeasurePreserving (switchingSplit last) volume (volume.prod volume) :=
  volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (complementaryControl last)

theorem slicePoint_complementaryControl (last : Fin 2) (w : ℝ) (δ : Fin 3 → ℝ) :
    slicePoint last w δ (complementaryControl last) = w := by
  fin_cases last <;> rfl

/-- Integrating the three active increments costs exactly the length of
the bounded complementary increment. -/
theorem volume_le_of_sliced_volume_le (last : Fin 2) (S : Set (Fin 4 → ℝ))
    (hS : MeasurableSet S) (I : Set ℝ) (hI : MeasurableSet I) (M : ENNReal)
    (hcomp : ∀ δ ∈ S, δ (complementaryControl last) ∈ I)
    (hslice : ∀ w ∈ I, volume (slicePoint last w ⁻¹' S) ≤ M) :
    volume S ≤ volume I * M := by
  let e := switchingSplit last
  let T := e.symm ⁻¹' S
  have hT : MeasurableSet T := hS.preimage e.symm.measurable
  have hvol : (volume.prod volume) T = volume S :=
    (MeasurePreserving.symm e (volume_preserving_switchingSplit last)).measure_preimage
      hS.nullMeasurableSet
  rw [← hvol, Measure.prod_apply hT]
  calc
    (∫⁻ w, volume (Prod.mk w ⁻¹' T)) ≤
        ∫⁻ w, I.indicator (fun _ => M) w := by
      apply lintegral_mono
      intro w
      change volume (Prod.mk w ⁻¹' T) ≤ I.indicator (fun _ => M) w
      have heq : Prod.mk w ⁻¹' T = slicePoint last w ⁻¹' S := by
        ext δ
        simp only [T, e, mem_preimage, switchingSplit_symm_apply]
      rw [heq]
      by_cases hw : w ∈ I
      · rw [Set.indicator_of_mem hw]
        exact hslice w hw
      · rw [Set.indicator_of_notMem hw]
        have hempty : slicePoint last w ⁻¹' S = ∅ := by
          ext δ
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          intro hδ
          apply hw
          simpa only [slicePoint_complementaryControl] using hcomp _ hδ
        simp only [hempty, measure_empty, le_refl]
    _ = volume I * M := by rw [lintegral_indicator_const hI, mul_comm]

/-- The full four-parameter endpoint bound. The endpoint cells may depend
on the frozen complementary increment; only their total base area is
bounded uniformly. -/
theorem four_parameter_endpoint_volume_le {ι : Type*}
    (v : Fin 4 → ℝ) (hv : v 1 - v 0 ≠ 0) (R : MvPolynomial (Fin 4) ℝ)
    (last : Fin 2) (D : ℕ) (hR : R.totalDegree ≤ D)
    (S : Set (Fin 4 → ℝ)) (I : Set ℝ) (F : Finset ι)
    (E : ℝ → ι → Set (Fin 2 → ℝ)) (c : ℝ → ι → ℝ) (B : ENNReal)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ)
    (hS : MeasurableSet S) (hI : MeasurableSet I)
    (hE : ∀ w ∈ I, ∀ i ∈ F, MeasurableSet (E w i))
    (harea : ∀ w ∈ I, (∑ i ∈ F, volume (E w i)) ≤ B)
    (hcomp : ∀ δ ∈ S, δ (complementaryControl last) ∈ I)
    (hcover : ∀ w ∈ I, ∀ δ : Fin 3 → ℝ, slicePoint last w δ ∈ S →
      ∃ i ∈ F,
        (![δ 0 + δ 1 + δ 2, v 0 * δ 0 + v 1 * δ 1 + v (Fin.natAdd 2 last) * δ 2]) ∈ E w i ∧
          |eval (slicePoint last w δ) R - c w i| ≤ ε)
    (hjac : ∀ δ ∈ S, κ ≤ |eval δ (endpointMinor R v (Fin.natAdd 2 last))|) :
    volume S ≤ volume I * B * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  rw [mul_assoc]
  apply volume_le_of_sliced_volume_le last S hS I hI _ hcomp
  intro w hw
  have hsm : MeasurableSet (slicePoint last w ⁻¹' S) := by
    apply hS.preimage
    unfold slicePoint
    fun_prop
  exact (sliced_endpoint_cells_volume_le v hv R last w D hR
    (slicePoint last w ⁻¹' S) F (E w) (c w) hε hκ hsm (hE w hw)
    (hcover w hw) (fun δ hδ => hjac _ hδ)).trans
      (mul_le_mul_of_nonneg_right (harea w hw) bot_le)

end Submission.Lib.K4ScalarSwitching.Switching
