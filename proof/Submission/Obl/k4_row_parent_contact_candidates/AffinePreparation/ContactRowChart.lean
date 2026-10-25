/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactRowChart.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Lib.K4ContactAffine.NativeCoarseBudget
import Submission.Lib.K4MovingMeshBoxes.Projection
import Submission.Lib.K4ContactNormalization.RowNormalization
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.AffineSheetPullback

/-! The parent row chart used only to prepare a coarse affine predictor.

The line and polynomial coordinate identities are adapted from this LOT
obligation, session x0776, `ZoomLabel.lean` and `ContactBaseMap.lean` on
origin/x0776 (17941c95). They are stated here for the accepted native zoom
type, without importing the contact-instance construction.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MvPolynomial Set Matrix MeasureTheory
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh (Zoom)
open Submission.Lib.K4ContactAffine (NativeSample)

noncomputable section

structure ContactRowChart where
  Z : Zoom
  B : Fin 2 → ℝ
  lam : ℝ

namespace ContactRowChart

variable (D : ContactRowChart)

def coeff (b : Fin 6 → ℝ) : Fin 6 → ℝ := skewCoeff D.B D.lam (D.Z.coeff b)

def test (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (unskewSubst D.B D.lam) (D.Z.push F)

def baseMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![D.Z.q⁻¹, 0, 0;
     0, D.Z.q⁻¹, 0;
     -(D.Z.c₃ / D.Z.w + D.B 0 / D.Z.q) / D.lam,
       -(D.Z.c₄ / D.Z.w + D.B 1 / D.Z.q) / D.lam, (D.Z.w * D.lam)⁻¹]

def baseShift : Fin 3 → ℝ :=
  ![-D.Z.t₀ / D.Z.q, -D.Z.z₀ / D.Z.q,
    (-D.Z.c₂ / D.Z.w + D.B 0 * D.Z.t₀ / D.Z.q + D.B 1 * D.Z.z₀ / D.Z.q) / D.lam]

theorem coeff_three (b : Fin 6 → ℝ) : D.coeff b 3 = b 3 := by
  simp [coeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff]

theorem coeff_contact (hlam : D.lam ≠ 0) (b : Fin 6 → ℝ) :
    D.coeff b 4 + D.coeff b 0 =
      (D.Z.coeff b 4 - D.B 0 - D.B 1 * b 3 + D.lam * D.Z.coeff b 0) / D.lam := by
  simp only [coeff, skewCoeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  field_simp

theorem degree_test (F : MvPolynomial (Fin 4) ℝ) :
    (D.test F).totalDegree ≤ F.totalDegree :=
  (degree_unskew_pullback D.B D.lam _).trans (D.Z.push_degree F)

theorem eval_test (hZ : D.Z.Ok) (hlam : D.lam ≠ 0) (F : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (D.coeff b) t) (D.test F) =
      D.Z.a⁻¹ * eval (point b (D.Z.untime t)) F := by
  rw [test, coeff, eval_unskew_pullback D.B hlam, D.Z.eval_push,
    D.Z.point_untime hZ, D.Z.unpos_pos hZ]

theorem eval_deriv_test (hZ : D.Z.Ok) (hlam : D.lam ≠ 0)
    (F : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (D.coeff b) t) (pderiv 3 (D.test F)) =
      eval (point b (D.Z.untime t)) (pderiv 3 F) := by
  rw [test, pderiv_unskew_pullback, coeff, eval_unskew_pullback D.B hlam,
    D.Z.pderiv_push hZ, Submission.Lib.K4ChartLifting.eval_bind₁', D.Z.eval_unsubst,
    D.Z.point_untime hZ, D.Z.unpos_pos hZ]

theorem eval_second_test (hZ : D.Z.Ok) (hlam : D.lam ≠ 0)
    (F : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (D.coeff b) t) (pderiv 3 (pderiv 3 (D.test F))) =
      D.Z.a * eval (point b (D.Z.untime t)) (pderiv 3 (pderiv 3 F)) := by
  rw [test, pderiv_unskew_pullback, pderiv_unskew_pullback, coeff,
    eval_unskew_pullback D.B hlam, D.Z.eval_pderiv_pderiv_push hZ,
    D.Z.point_untime hZ, D.Z.unpos_pos hZ]

theorem point_coeff (hZ : D.Z.Ok) (hlam : D.lam ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    point (D.coeff b) (D.Z.time t) =
      affineHiddenPoint D.baseMatrix D.baseShift D.Z.h₀ D.Z.a (point b t) := by
  have hq := hZ.q_ne
  have hw := hZ.w_ne
  funext i
  fin_cases i <;>
    simp [coeff, skewCoeff, point, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time, affineHiddenPoint,
      Submission.Lib.K4AffineMeshCaps.affineBase, baseMatrix, baseShift,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Function.comp_def] <;>
    field_simp <;> ring

theorem base_coeff (hZ : D.Z.Ok) (hlam : D.lam ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    Submission.Lib.K4QuadraticSheetCore.lineP (D.coeff b) (D.Z.time t) =
      Submission.Lib.K4AffineMeshCaps.affineBase D.baseMatrix D.baseShift
        (Submission.Lib.K4MovingMeshBoxes.basePoint b t) := by
  have hcast : (point b t ∘ Fin.castSucc) =
      Submission.Lib.K4MovingMeshBoxes.basePoint b t := by
    funext i
    fin_cases i <;> rfl
  have h := D.point_coeff hZ hlam b t
  funext i
  have hi := congrFun h i.castSucc
  dsimp only [affineHiddenPoint] at hi
  rw [hcast] at hi
  fin_cases i <;>
    simpa [Submission.Lib.K4QuadraticSheetCore.lineP, point, affineHiddenPoint,
      Submission.Lib.K4MovingMeshBoxes.basePoint, Function.comp_def] using hi

theorem det_baseMatrix : D.baseMatrix.det = D.Z.q⁻¹ * D.Z.q⁻¹ * (D.Z.w * D.lam)⁻¹ := by
  simp [baseMatrix, Matrix.det_fin_three]

theorem det_baseMatrix_ne (hZ : D.Z.Ok) (hlam : D.lam ≠ 0) : D.baseMatrix.det ≠ 0 := by
  rw [D.det_baseMatrix]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hZ.q_ne) (inv_ne_zero hZ.q_ne))
    (inv_ne_zero (mul_ne_zero hZ.w_ne hlam))

theorem abs_det_inv (hq : 0 < D.Z.q) (hw : 0 < D.Z.w) :
    |D.baseMatrix.det|⁻¹ = |D.lam| * D.Z.q ^ 2 * D.Z.w := by
  simp only [D.det_baseMatrix, abs_mul, abs_inv, abs_of_pos hq, abs_of_pos hw,
    mul_inv, inv_inv]
  ring

theorem time_mem (hq : 0 < D.Z.q) {t : ℝ}
    (ht : t ∈ Icc D.Z.t₀ (D.Z.t₀ + D.Z.q)) : D.Z.time t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr ht.1) hq.le
  · exact (div_le_one hq).mpr (by linarith [ht.2])

theorem untime_mem (hq : 0 < D.Z.q) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    D.Z.untime t ∈ Icc D.Z.t₀ (D.Z.t₀ + D.Z.q) := by
  constructor <;> dsimp [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.untime] <;> nlinarith [ht.1, ht.2]

def sample {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (π : Measure ℝ)
    (b : Ω → Fin 6 → ℝ) (time : Ω → ℝ) (F : MvPolynomial (Fin 4) ℝ) : NativeSample Ω where
  μ := μ
  π := π
  b := fun p => D.coeff (b p)
  time := fun p => D.Z.time (time p)
  P := D.test F

/-- Parent full-time fits and observed regularity become the unit-width
native hypotheses; the original incidence law and palette do not move. -/
theorem sample_good {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (π : Measure ℝ)
    (b : Ω → Fin 6 → ℝ) (time : Ω → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hZ : D.Z.Ok) (hlam : D.lam ≠ 0) (hq : 0 < D.Z.q) (ha : 0 < D.Z.a)
    {K H E : ℝ} (hK : 0 < K) (hKH : K ≤ H) (p : Ω)
    (ht : time p ∈ Icc D.Z.t₀ (D.Z.t₀ + D.Z.q))
    (hcoeff : |D.coeff (b p) 0| + |D.coeff (b p) 1| + |D.coeff (b p) 3| +
      |D.coeff (b p) 4| ≤ H)
    (hfit : ∀ t ∈ Icc D.Z.t₀ (D.Z.t₀ + D.Z.q),
      |eval (point (b p) t) F| ≤ K * D.Z.a ∧
      |eval (point (b p) t) (pderiv 3 F)| ≤ K ∧
      |eval (point (b p) t) (pderiv 3 (pderiv 3 F))| ≤ K / D.Z.a)
    (hreg : K⁻¹ ≤ |eval (point (b p) (time p)) (pderiv 3 F)|)
    (hrow : |D.Z.coeff (b p) 4 - D.B 0 - D.B 1 * b p 3 +
      D.lam * D.Z.coeff (b p) 0| ≤ E) :
    (D.sample μ π b time F).Good H (E * |D.lam⁻¹|) p := by
  change (D.Z.time (time p) ∈ Icc (0 : ℝ) 1) ∧ _
  dsimp only [sample]
  refine ⟨D.time_mem hq ht, hcoeff, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨h0, h1, h2⟩ := hfit (D.Z.untime t) (D.untime_mem hq ht)
    rw [D.eval_test hZ hlam, D.eval_deriv_test hZ hlam, D.eval_second_test hZ hlam]
    refine ⟨?_, h1.trans hKH, ?_⟩
    · rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
      calc D.Z.a⁻¹ * |eval (point (b p) (D.Z.untime t)) F| ≤ D.Z.a⁻¹ * (K * D.Z.a) :=
            mul_le_mul_of_nonneg_left h0 (inv_nonneg.mpr ha.le)
        _ = K := by field_simp
        _ ≤ H := hKH
    · rw [abs_mul, abs_of_pos ha]
      calc D.Z.a * |eval (point (b p) (D.Z.untime t)) (pderiv 3 (pderiv 3 F))| ≤
            D.Z.a * (K / D.Z.a) := mul_le_mul_of_nonneg_left h2 ha.le
        _ = K := by field_simp
        _ ≤ H := hKH
  · rw [D.eval_deriv_test hZ hlam, D.Z.untime_time hZ]
    exact (inv_anti₀ hK hKH).trans hreg
  · rw [D.coeff_contact hlam, div_eq_mul_inv, abs_mul]
    exact mul_le_mul_of_nonneg_right hrow (abs_nonneg _)


/-- The row chart resolves a source mesh using only horizontal parent and
row bounds. Adapted from x0776's `ContactCaps.baseMat_resolve`, 17941c95. -/
theorem baseMatrix_resolve {q g K M₁ δ σ : ℝ}
    (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1) (hK : 1 ≤ K) (hM₁ : 1 ≤ M₁)
    (hZq : D.Z.q = q) (hZw : D.Z.w = q * g)
    (h3 : |D.Z.c₃| ≤ K) (h4 : |D.Z.c₄| ≤ K)
    (hB : |D.B 0| + |D.B 1| ≤ M₁) (hlam : |D.lam⁻¹| ≤ M₁) (hδ : 0 ≤ δ)
    (hres : (2 * K + M₁ + 1) * M₁ * δ ≤ q * g * σ) :
    ∀ i, (∑ j, |D.baseMatrix i j| * δ) ≤ σ := by
  have hqg : 0 < q * g := mul_pos hq hg
  have hδq : δ ≤ q * σ := by
    have h1 : δ ≤ (2 * K + M₁ + 1) * M₁ * δ := by
      have : 1 ≤ (2 * K + M₁ + 1) * M₁ := by nlinarith
      nlinarith
    have hσ : 0 ≤ σ := by
      have h0 : 0 ≤ (2 * K + M₁ + 1) * M₁ * δ := by positivity
      by_contra hneg
      have : q * g * σ < 0 := mul_neg_of_pos_of_neg hqg (lt_of_not_ge hneg)
      linarith
    have h2 : q * g * σ ≤ q * σ := by
      have := mul_le_mul_of_nonneg_left hg1 hq.le
      nlinarith
    linarith
  intro i
  fin_cases i
  · simp [baseMatrix, Fin.sum_univ_three, hZq]
    rw [abs_of_pos hq, inv_mul_le_iff₀ hq]
    linarith
  · simp [baseMatrix, Fin.sum_univ_three, hZq]
    rw [abs_of_pos hq, inv_mul_le_iff₀ hq]
    linarith
  · simp [baseMatrix, Fin.sum_univ_three, hZq, hZw]
    have e1 : ∀ x y : ℝ, |(-(x / q) + -(y / (q * g))) / D.lam| = |g * x + y| / (q * g) * |D.lam⁻¹| := by
      intro x y
      rw [div_eq_mul_inv, abs_mul]
      congr 1
      rw [show -(x / q) + -(y / (q * g)) = -((g * x + y) / (q * g)) by field_simp; ring]
      rw [abs_neg, abs_div, abs_of_pos hqg]
    have e2 : |D.lam|⁻¹ * (|g|⁻¹ * |q|⁻¹) = 1 / (q * g) * |D.lam⁻¹| := by
      rw [abs_inv D.lam, abs_of_pos hg, abs_of_pos hq]; ring
    rw [e1, e1, e2]
    have hx : ∀ x y : ℝ, |y| ≤ K → |g * x + y| ≤ |x| + K := by
      intro x y hy
      calc |g * x + y| ≤ |g * x| + |y| := abs_add_le _ _
        _ ≤ |x| + K := by
          rw [abs_mul, abs_of_pos hg]
          have : g * |x| ≤ |x| := by nlinarith [abs_nonneg x]
          linarith
    have hx0 := hx (D.B 0) D.Z.c₃ h3
    have hx1 := hx (D.B 1) D.Z.c₄ h4
    have hu := abs_nonneg D.lam⁻¹
    calc |g * D.B 0 + D.Z.c₃| / (q * g) * |D.lam⁻¹| * δ + |g * D.B 1 + D.Z.c₄| / (q * g) * |D.lam⁻¹| * δ +
          1 / (q * g) * |D.lam⁻¹| * δ
        = (|g * D.B 0 + D.Z.c₃| + |g * D.B 1 + D.Z.c₄| + 1) * |D.lam⁻¹| * δ / (q * g) := by ring
      _ ≤ (2 * K + M₁ + 1) * M₁ * δ / (q * g) := by
          apply div_le_div_of_nonneg_right _ hqg.le
          apply mul_le_mul_of_nonneg_right _ hδ
          apply mul_le_mul _ hlam hu (by positivity)
          linarith
      _ ≤ σ := by rw [div_le_iff₀ hqg]; linarith


/-- Uniform bound for all three row-matrix sums. -/
theorem row_sum_le {q g K M : ℝ}
    (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hZq : D.Z.q = q) (hZw : D.Z.w = q * g)
    (h3 : |D.Z.c₃| ≤ K) (h4 : |D.Z.c₄| ≤ K)
    (hB : |D.B 0| + |D.B 1| ≤ M) (hlam : |D.lam⁻¹| ≤ M) :
    ∀ i, (∑ j, |D.baseMatrix i j|) ≤ (2 * K + M + 1) * M / (q * g) := by
  have hres : (2 * K + M + 1) * M * 1 ≤
      q * g * ((2 * K + M + 1) * M / (q * g)) := by
    field_simp [(mul_pos hq hg).ne']
    norm_num
  simpa only [mul_one] using D.baseMatrix_resolve hq hg hg1 hK hM hZq hZw h3 h4 hB hlam
    (show (0 : ℝ) ≤ 1 by norm_num) hres

/-- Return the coarse palette to full original trajectories over the
parent's original block. This uses no bound on the affine coefficients. -/
theorem cover_pullback {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (π : Measure ℝ) (b : Ω → Fin 6 → ℝ) (time : Ω → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) (hZ : D.Z.Ok) (hlam : D.lam ≠ 0)
    (hq : 0 < D.Z.q) {E : ℝ} (hcover : (D.sample μ π b time F).Cover E) :
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ᵐ p ∂μ, ∃ i : Fin 3,
      ∀ t ∈ Icc D.Z.t₀ (D.Z.t₀ + D.Z.q),
        |eval (point (b p) t) (affineBase (L i)) - point (b p) t 3| ≤ |D.Z.a| * E := by
  obtain ⟨L, hL⟩ := hcover
  refine ⟨fun i => affinePredictorPullback D.baseMatrix D.baseShift D.Z.h₀ D.Z.a (L i), ?_⟩
  filter_upwards [hL] with p hp
  obtain ⟨i, hi⟩ := hp
  refine ⟨i, ?_⟩
  intro t ht
  apply affinePredictorPullback_fit D.baseMatrix D.baseShift D.Z.h₀ D.Z.a hZ.a_ne
    (L i) (point (b p) t)
  rw [← D.point_coeff hZ hlam]
  have h := hi (D.Z.time t) (D.time_mem hq ht)
  simpa [sample, affineBase, point, abs_sub_comm] using h

end ContactRowChart

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
