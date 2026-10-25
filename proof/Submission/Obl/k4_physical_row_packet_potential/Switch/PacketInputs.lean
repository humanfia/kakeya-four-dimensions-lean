-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketInputs.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Generic inputs of the packet switching:

* `floor_eq_abs_sub_lt`, `physicalCode_geom`: events with one frozen physical
  code share base and height up to the code mesh;
* `velBin`, `binDir`: control by planar velocity bins, with their errors;
* `field_bounds_of_coeff`: value and Lipschitz bounds of a polynomial field
  with bounded coefficients on a box;
* `cap_of_ceiling`: a base density ceiling on `ℝ³` (Euclidean) gives the
  rescaled-base cap used by the switching norming.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketSwitching
import Submission.Obl.k4_physical_row_packet_potential.Switch.StripBreadth
import Submission.Obl.k4_physical_row_packet_potential.Switch.SupportCover
import Submission.Lib.K4CubicTests.FinitePolynomialBounds
import Submission.Lib.K4CubicTests.PolynomialPerturbation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal Pointwise

noncomputable section

namespace PacketSwitching

/-- Differentiation does not raise the total degree. -/
theorem totalDegree_pderiv_le_of (F : MvPolynomial (Fin 3) ℝ) (k : Fin 3) {D : ℕ}
    (hF : F.totalDegree ≤ D) : (pderiv k F).totalDegree ≤ D := by
  classical
  apply Finset.sup_le
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  have hne : F.coeff (m + Finsupp.single k 1) ≠ 0 := fun h => hm (by rw [h, zero_mul])
  have hle := le_totalDegree (mem_support_iff.mpr hne)
  have hsum : (m + Finsupp.single k 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

/-- Equal floors at mesh `m` are closer than `m`. -/
theorem floor_eq_abs_sub_lt {x y m : ℝ} (hm : 0 < m) (h : ⌊x / m⌋ = ⌊y / m⌋) :
    |x - y| < m := by
  have hx1 := Int.floor_le (x / m)
  have hx2 := Int.lt_floor_add_one (x / m)
  have hy1 := Int.floor_le (y / m)
  have hy2 := Int.lt_floor_add_one (y / m)
  rw [h] at hx1 hx2
  have hxy : |x / m - y / m| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have heq : x / m - y / m = (x - y) / m := by ring
  rw [heq, abs_div, abs_of_pos hm, div_lt_one hm] at hxy
  exact hxy

/-- Events with one frozen physical code share base and height. -/
theorem physicalCode_geom (zb : Ev → P3) (Xn : Ev → ℝ) {ε : ℝ} (hε : 0 < ε) {z z' : Ev}
    (h : physicalCode zb Xn ε z = physicalCode zb Xn ε z') :
    ‖(fun i => zb z i) - (fun i => zb z' i)‖ ≤ ε ∧ |Xn z - Xn z'| ≤ ε := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine ⟨?_, (floor_eq_abs_sub_lt hε h2).le⟩
  refine (pi_norm_le_iff_of_nonneg hε.le).mpr (fun i => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact (floor_eq_abs_sub_lt hε (congrFun h1 i)).le

/-- The planar velocity bin of a line at width `pv`. -/
def velBin (pv : ℝ) (l : Ln) : Fin 2 → ℤ := fun i => ⌊v l i / pv⌋

/-- The lifted direction `(1, center)` of a velocity bin. -/
def binDir (pv : ℝ) (c : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  liftDir (WithLp.toLp 2 (fun i => pv * ((c i : ℝ) + 1 / 2)))

theorem binDir_zero (pv : ℝ) (c : Fin 2 → ℤ) : binDir pv c 0 = 1 := rfl

theorem binDir_one (pv : ℝ) (c : Fin 2 → ℤ) : binDir pv c 1 = pv * ((c 0 : ℝ) + 1 / 2) := rfl

theorem binDir_two (pv : ℝ) (c : Fin 2 → ℤ) : binDir pv c 2 = pv * ((c 1 : ℝ) + 1 / 2) := rfl

theorem measurable_velBin (pv : ℝ) : Measurable (velBin pv) := by
  apply measurable_pi_iff.mpr
  intro i
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  fin_cases i
  · exact ((continuous_apply 3).comp continuous_snd).measurable
  · exact ((continuous_apply 4).comp continuous_snd).measurable

theorem v_apply_zero (l : Ln) : v l 0 = l.2 3 := rfl

theorem v_apply_one (l : Ln) : v l 1 = l.2 4 := rfl

theorem bin_center_dist {pv : ℝ} (hpv : 0 < pv) (l : Ln) (i : Fin 2) :
    |v l i - pv * ((velBin pv l i : ℝ) + 1 / 2)| ≤ pv / 2 :=
  floor_cell_center_dist hpv

/-- The bin direction is within `pv / 2` of the true direction, coordinatewise. -/
theorem direction_binDir_le {pv : ℝ} (hpv : 0 < pv) (l : Ln) :
    ‖direction l - (fun i : Fin 3 => binDir pv (velBin pv l) i)‖ ≤ pv / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr (fun i => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs]
  fin_cases i
  · simp [direction, binDir, liftDir]; linarith
  · have h := bin_center_dist hpv l 0
    simpa [direction, binDir, liftDir, v_apply_zero] using h
  · have h := bin_center_dist hpv l 1
    simpa [direction, binDir, liftDir, v_apply_one] using h

/-- The coordinates of a bin direction are bounded by the velocity bound plus one bin. -/
theorem binDir_coord_le {pv U : ℝ} (hpv : 0 < pv) {l : Ln} (hvl : ‖v l‖ ≤ U) (i : Fin 3) :
    |binDir pv (velBin pv l) i| ≤ max 1 (U + pv) := by
  fin_cases i
  · change |binDir pv (velBin pv l) 0| ≤ _
    rw [binDir_zero, abs_one]
    exact le_max_left _ _
  · have h := bin_center_dist hpv l 0
    have hv0 : |v l 0| ≤ U := by
      have := PiLp.norm_apply_le (v l) 0
      rw [Real.norm_eq_abs] at this
      exact this.trans hvl
    change |binDir pv (velBin pv l) 1| ≤ _
    rw [binDir_one]
    rw [abs_le] at h hv0 ⊢
    constructor <;> nlinarith [le_max_right 1 (U + pv)]
  · have h := bin_center_dist hpv l 1
    have hv1 : |v l 1| ≤ U := by
      have := PiLp.norm_apply_le (v l) 1
      rw [Real.norm_eq_abs] at this
      exact this.trans hvl
    change |binDir pv (velBin pv l) 2| ≤ _
    rw [binDir_two]
    rw [abs_le] at h hv1 ⊢
    constructor <;> nlinarith [le_max_right 1 (U + pv)]

/-- The Euclidean distance from the bin direction to the true lifted
direction is at most `pv`. -/
theorem binDir_dist_le {pv : ℝ} (hpv : 0 < pv) (l : Ln) :
    ‖binDir pv (velBin pv l) - liftDir (v l)‖ ≤ pv := by
  have h0 := bin_center_dist hpv l 0
  have h1 := bin_center_dist hpv l 1
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by linarith), Fin.sum_univ_three]
  simp only [binDir, liftDir, PiLp.sub_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    sub_self, norm_zero, Real.norm_eq_abs]
  rw [abs_sub_comm] at h0 h1
  have e0 : |pv * ((velBin pv l 0 : ℝ) + 1 / 2) - v l 0| ^ 2 ≤ (pv / 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : |pv * ((velBin pv l 1 : ℝ) + 1 / 2) - v l 1| ^ 2 ≤ (pv / 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [e0, e1]

/-- Coefficient bounds give value and Lipschitz bounds of a field on a box. -/
theorem field_bounds_of_coeff (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (D : ℕ)
    (hT : ∀ i, (Tf i).totalDegree ≤ D) {AT R : ℝ} (hAT : 0 ≤ AT) (hR : 0 ≤ R)
    (hcoeff : ∀ i m, |(Tf i).coeff m| ≤ AT) :
    (∀ x ∈ Metric.closedBall (0 : Fin 3 → ℝ) R, ∀ i,
      |eval x (Tf i)| ≤ (D + 1 : ℕ) * (max 1 (3 * R)) ^ D * AT) ∧
    (∀ x ∈ Metric.closedBall (0 : Fin 3 → ℝ) R, ∀ y ∈ Metric.closedBall (0 : Fin 3 → ℝ) R, ∀ i,
      |eval x (Tf i) - eval y (Tf i)| ≤
        (3 * ((D + 1 : ℕ) * (max 1 (3 * R)) ^ D * ((D : ℝ) * AT))) * ‖x - y‖) := by
  have hcoord {x : Fin 3 → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) (k : Fin 3) :
      |x k| ≤ R := by
    rw [mem_closedBall_zero_iff] at hx
    have := norm_le_pi_norm x k
    rw [Real.norm_eq_abs] at this
    exact this.trans hx
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  refine ⟨fun x hx i => ?_, fun x hx y hy i => ?_⟩
  · have h := Submission.Lib.K4CubicTests.finite_polynomial_eval_abs_le (Tf i) D (hT i) R AT hR
      hAT (hcoeff i) x (hcoord hx)
    rwa [hcard] at h
  · set Bd := ((D + 1 : ℕ) : ℝ) * (max 1 (3 * R)) ^ D * ((D : ℝ) * AT) with hBd
    have hBd0 : 0 ≤ Bd := by positivity
    let z : ℝ → Fin 3 → ℝ := fun t k => y k + t * (x k - y k)
    have hzc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 3) : |z t k| ≤ R := by
      have heq : z t k = (1 - t) * y k + t * x k := by dsimp [z]; ring
      rw [heq]
      calc
        _ ≤ |(1 - t) * y k| + |t * x k| := abs_add_le _ _
        _ = (1 - t) * |y k| + t * |x k| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
        _ ≤ (1 - t) * R + t * R := add_le_add
          (mul_le_mul_of_nonneg_left (hcoord hy k) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (hcoord hx k) ht.1)
        _ = R := by ring
    have hdv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 3) :
        |eval (z t) (pderiv k (Tf i))| ≤ Bd := by
      have hdeg : (pderiv k (Tf i)).totalDegree ≤ D :=
        totalDegree_pderiv_le_of (Tf i) k (hT i)
      have hdc : ∀ m, |(pderiv k (Tf i)).coeff m| ≤ (D : ℝ) * AT :=
        fun m => Submission.Lib.K4CubicTests.coeff_pderiv_abs_le_of_totalDegree (Tf i) D (hT i)
          AT hAT (hcoeff i) k m
      have h := Submission.Lib.K4CubicTests.finite_polynomial_eval_abs_le (pderiv k (Tf i)) D
        hdeg R ((D : ℝ) * AT) hR (by positivity) hdc (z t) (hzc t ht)
      rwa [hcard] at h
    have hzd (t : ℝ) (k : Fin 3) : HasDerivAt (fun s => z s k) (x k - y k) t := by
      simpa only [z, one_mul, id_eq] using
        HasDerivAt.const_add (y k) ((hasDerivAt_id t).mul_const (x k - y k))
    have hf (t : ℝ) := Submission.Lib.K4CubicTests.hasDerivAt_eval_polynomial_curve (Tf i) z
      (fun k => x k - y k) t (hzd t)
    have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
        ‖∑ k : Fin 3, eval (z t) (pderiv k (Tf i)) * (x k - y k)‖ ≤ 3 * (Bd * ‖x - y‖) := by
      rw [Real.norm_eq_abs]
      calc
        _ ≤ ∑ k : Fin 3, |eval (z t) (pderiv k (Tf i)) * (x k - y k)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin 3, Bd * ‖x - y‖ := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          have hk : |x k - y k| ≤ ‖x - y‖ := by
            have := norm_le_pi_norm (x - y) k
            rwa [Pi.sub_apply, Real.norm_eq_abs] at this
          exact mul_le_mul (hdv t ⟨ht.1, ht.2.le⟩ k) hk (abs_nonneg _) hBd0
        _ = 3 * (Bd * ‖x - y‖) := by simp
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hf t).hasDerivWithinAt) hbound
    have hz0 : z 0 = y := by funext k; simp [z]
    have hz1 : z 1 = x := by funext k; dsimp [z]; ring
    simp only [hz0, hz1, Real.norm_eq_abs] at hmv
    calc
      _ ≤ 3 * (Bd * ‖x - y‖) := hmv
      _ = _ := by ring

/-- A base density ceiling on Euclidean `ℝ³` caps the law of the rescaled
coordinate base. -/
theorem cap_of_ceiling {X : Type*} [MeasurableSpace X] (μ : Measure X) (zb : X → P3)
    (hzb : Measurable zb) {Kc : ENNReal}
    (hceil : ∀ U : Set P3, MeasurableSet U → μ {x | zb x ∈ U} ≤ Kc * volume U)
    {Rb : ℝ} (hRb : 0 < Rb) :
    μ.map (fun x => fun i => Rb⁻¹ * zb x i) ≤ (Kc * ENNReal.ofReal (Rb ^ 3)) • volume := by
  have hf : Measurable (fun x => fun i => Rb⁻¹ * zb x i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.mul ((PiLp.continuous_apply 2 _ i).measurable.comp hzb)
  rw [Measure.le_iff]
  intro V hV
  rw [Measure.map_apply hf hV, Measure.smul_apply, smul_eq_mul]
  let W : Set (Fin 3 → ℝ) := (fun y : Fin 3 → ℝ => Rb⁻¹ • y) ⁻¹' V
  have hW : MeasurableSet W := (measurable_const_smul Rb⁻¹) hV
  let U : Set P3 := WithLp.ofLp ⁻¹' W
  have hU : MeasurableSet U := (PiLp.continuous_ofLp 2 _).measurable hW
  have hpre : (fun x => fun i => Rb⁻¹ * zb x i) ⁻¹' V = {x | zb x ∈ U} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, U, W]
    rfl
  rw [hpre]
  refine (hceil U hU).trans ?_
  have hvolU : volume U = volume W :=
    (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hW.nullMeasurableSet
  have hWeq : W = Rb • V := preimage_smul_inv₀ hRb.ne' V
  rw [hvolU, hWeq, Measure.addHaar_smul_of_nonneg _ hRb.le]
  simp only [Module.finrank_fin_fun]
  rw [mul_assoc]

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
