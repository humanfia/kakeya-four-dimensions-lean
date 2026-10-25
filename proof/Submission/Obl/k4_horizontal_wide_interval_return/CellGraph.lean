/- Adapted within this LOT tree from o218/x0764, commit a57aabc6806d303a53728cab0d5e6ea27469d825,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/CellGraph.lean. -/
import Submission.Obl.k4_horizontal_wide_interval_return.CellFrame
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers
import Submission.Lib.K4ChartLifting.PolyAlgebra

set_option linter.unusedVariables false

/-!
# Returning a cell prediction to a quadratic graph in the true base

After scalar projection inside a true cell one has a quadratic `P(z_t, z_Z)` predicting the
normalized signal `sig = (X - fit)/a - P_nc`.  Then `X ≈ fit + a (P_nc + P(z_t, z_Z))`, which is a
polynomial `cellGraph P` of degree `≤ 2` in the true base `(t, Z, Y)`.  This file builds it, proves
the exact identity `X - cellGraph P = a (sig - P(z_t, z_Z))`, the degree bound, and an `ℓ¹`
coefficient bound `≤ 53 H³/(q² g²)` (all frame data and `‖P‖₁` bounded by `H`), which is what
`GraphReturn.native_candidate_of_graph_mass` (x0760) needs.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MvPolynomial Submission.Lib.K4ChartLifting

namespace CellFrame

variable (F : CellFrame)

/-- `z_t`, `z_Z`, `U` and the fit as polynomials in the true base `(t, Z, Y)`. -/
noncomputable def ztPoly : MvPolynomial (Fin 3) ℝ := MvPolynomial.C F.q⁻¹ * (X 0 - MvPolynomial.C F.t₀)
noncomputable def zZPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C F.q⁻¹ * (X 1 - MvPolynomial.C (F.c 0) - X 0 * MvPolynomial.C (F.c 1))
noncomputable def UPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (F.q * F.g)⁻¹ * (X 2 - MvPolynomial.C (F.c 2) - X 0 * MvPolynomial.C (F.c 3) - MvPolynomial.C (F.c 4) * X 1)
noncomputable def fitPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (F.L 0) + MvPolynomial.C (F.L 1) * X 0 + MvPolynomial.C (F.L 2) * X 1 + MvPolynomial.C (F.L 3) * X 2
noncomputable def PncPoly : MvPolynomial (Fin 3) ℝ :=
  (MvPolynomial.C (F.C 0) + MvPolynomial.C (F.C 1) * F.ztPoly + MvPolynomial.C (F.C 2) * F.zZPoly) * F.UPoly + MvPolynomial.C (F.C 3) * F.UPoly ^ 2

/-- The substitution `(z_t, z_Z)` of a scalar polynomial. -/
noncomputable def cellSubst : Fin 2 → MvPolynomial (Fin 3) ℝ := ![F.ztPoly, F.zZPoly]

/-- The returned graph `fit + a (P_nc + P(z_t, z_Z))`. -/
noncomputable def cellGraph (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  F.fitPoly + MvPolynomial.C F.a * (F.PncPoly + bind₁ F.cellSubst P)

variable {F}

theorem eval_ztPoly (y : Fin 3 → ℝ) : eval y F.ztPoly = F.zt (y 0) := by
  simp [ztPoly, zt, div_eq_inv_mul]

theorem eval_zZPoly (y : Fin 3 → ℝ) : eval y F.zZPoly = F.zZ (y 0) (y 1) := by
  simp [zZPoly, zZ, div_eq_inv_mul]

theorem eval_UPoly (y : Fin 3 → ℝ) : eval y F.UPoly = F.U (y 0) (y 1) (y 2) := by
  simp [UPoly, U, div_eq_inv_mul]

theorem eval_fitPoly (y : Fin 3 → ℝ) : eval y F.fitPoly = F.fit (y 0) (y 1) (y 2) := by
  simp [fitPoly, fit]

theorem eval_PncPoly (y : Fin 3 → ℝ) : eval y F.PncPoly = F.Pnc (y 0) (y 1) (y 2) := by
  simp [PncPoly, Pnc, eval_ztPoly, eval_zZPoly, eval_UPoly]

theorem eval_bind_cellSubst (P : MvPolynomial (Fin 2) ℝ) (y : Fin 3 → ℝ) :
    eval y (bind₁ F.cellSubst P) = eval ![F.zt (y 0), F.zZ (y 0) (y 1)] P := by
  change eval₂Hom (RingHom.id ℝ) y _ = eval₂Hom (RingHom.id ℝ) _ P
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 2 → ℝ => eval₂Hom (RingHom.id ℝ) f P)
  funext i
  fin_cases i
  · simp [cellSubst, eval_ztPoly]
  · simp [cellSubst, eval_zZPoly]

/-- The exact return identity. -/
theorem sub_eval_cellGraph (ha : F.a ≠ 0) (P : MvPolynomial (Fin 2) ℝ) (t Z Y Xh : ℝ) :
    Xh - eval ![t, Z, Y] (F.cellGraph P) =
      F.a * (F.sig t Z Y Xh - eval ![F.zt t, F.zZ t Z] P) := by
  simp only [cellGraph, map_add, map_mul, eval_C, eval_fitPoly, eval_PncPoly,
    eval_bind_cellSubst, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sig, resid]
  field_simp
  ring

theorem totalDegree_cellGraph (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    (F.cellGraph P).totalDegree ≤ 2 := by
  have hlin1 : ∀ (a b : ℝ) (i : Fin 3), (MvPolynomial.C a * (X i - MvPolynomial.C b) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    intro a b i
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
  have hzt : F.ztPoly.totalDegree ≤ 1 := hlin1 _ _ _
  have hzZ : F.zZPoly.totalDegree ≤ 1 := by
    unfold zZPoly
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
      (max_le (by simp) (by simp))) ?_)
    exact (totalDegree_mul _ _).trans (by simp)
  have hU : F.UPoly.totalDegree ≤ 1 := by
    unfold UPoly
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
      (max_le ((totalDegree_sub _ _).trans (max_le (by simp) (by simp)))
        ((totalDegree_mul _ _).trans (by simp)))) ((totalDegree_mul _ _).trans (by simp)))
  have hCmul : ∀ (c : ℝ) (p : MvPolynomial (Fin 3) ℝ), (MvPolynomial.C c * p).totalDegree ≤ p.totalDegree :=
    fun c p => (totalDegree_mul _ _).trans (by simp)
  have hfit : F.fitPoly.totalDegree ≤ 2 := by
    unfold fitPoly
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (by simp) ((hCmul _ _).trans (by simp))))
      ((hCmul _ _).trans (by simp)))) ((hCmul _ _).trans (by simp)))
  have hα : (MvPolynomial.C (F.C 0) + MvPolynomial.C (F.C 1) * F.ztPoly + MvPolynomial.C (F.C 2) * F.zZPoly).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (by simp) ((hCmul _ _).trans hzt))) ((hCmul _ _).trans hzZ))
  have hPnc : F.PncPoly.totalDegree ≤ 2 := by
    unfold PncPoly
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · have := add_le_add hα hU; omega
    · refine (hCmul _ _).trans ((totalDegree_pow _ _).trans ?_)
      have := Nat.mul_le_mul_left 2 hU; omega
  have hbind : (bind₁ F.cellSubst P).totalDegree ≤ 2 := by
    refine (Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _ ?_ _).trans hP
    intro i; fin_cases i
    · exact hzt
    · exact hzZ
  unfold cellGraph
  exact (totalDegree_add _ _).trans (max_le hfit ((hCmul _ _).trans
    ((totalDegree_add _ _).trans (max_le hPnc hbind))))

/-- The `ℓ¹` coefficient bound of the returned graph: with all frame data and `‖P‖₁` bounded by
`H ≥ 1`, `0 < q, g ≤ 1` and `0 < a ≤ 1`, `‖cellGraph P‖₁ ≤ 53 H³ (q g)⁻²`. -/
theorem coeffL1_cellGraph {H : ℝ} (hH : 1 ≤ H) (hq : 0 < F.q) (hq1 : F.q ≤ 1) (hg : 0 < F.g)
    (hg1 : F.g ≤ 1) (ha : 0 < F.a) (ha1 : F.a ≤ 1) (ht₀ : |F.t₀| ≤ H)
    (hc : ∀ i, |F.c i| ≤ H) (hL : ∀ i, |F.L i| ≤ H) (hC : ∀ i, |F.C i| ≤ H)
    (P : MvPolynomial (Fin 2) ℝ) (hPdeg : P.totalDegree ≤ 2) (hP : coeffL1 P ≤ H) :
    coeffL1 (F.cellGraph P) ≤ 53 * H ^ 3 * ((F.q * F.g)⁻¹) ^ 2 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hqg : 0 < F.q * F.g := mul_pos hq hg
  set Q := (F.q * F.g)⁻¹ with hQdef
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]; exact one_le_inv₀ hqg |>.mpr (by nlinarith)
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1
  have hqinv : F.q⁻¹ ≤ Q := by
    rw [hQdef]; exact inv_anti₀ hqg (by nlinarith)
  have hqinv0 : 0 ≤ F.q⁻¹ := inv_nonneg.mpr hq.le
  have habsq : |F.q⁻¹| = F.q⁻¹ := abs_of_nonneg hqinv0
  -- the three coordinates
  have hzt : coeffL1 F.ztPoly ≤ 2 * H * Q := by
    unfold ztPoly
    refine (coeffL1_C_mul_le _ _).trans ?_
    rw [habsq]
    have h1 : coeffL1 (X 0 - MvPolynomial.C F.t₀ : MvPolynomial (Fin 3) ℝ) ≤ 1 + H := by
      refine (coeffL1_sub_le _ _).trans ?_
      rw [coeffL1_X, coeffL1_C]; linarith
    calc F.q⁻¹ * coeffL1 (X 0 - MvPolynomial.C F.t₀ : MvPolynomial (Fin 3) ℝ)
        ≤ Q * (1 + H) := mul_le_mul hqinv h1 (coeffL1_nonneg _) hQ0
      _ ≤ 2 * H * Q := by nlinarith
  have hzZ : coeffL1 F.zZPoly ≤ 3 * H * Q := by
    unfold zZPoly
    refine (coeffL1_C_mul_le _ _).trans ?_
    rw [habsq]
    have h1 : coeffL1 (X 1 - MvPolynomial.C (F.c 0) - X 0 * MvPolynomial.C (F.c 1) :
        MvPolynomial (Fin 3) ℝ) ≤ 1 + H + H := by
      refine (coeffL1_sub_le _ _).trans (add_le_add ((coeffL1_sub_le _ _).trans ?_) ?_)
      · rw [coeffL1_X, coeffL1_C]; linarith [hc 0]
      · refine (coeffL1_mul_le _ _).trans ?_
        rw [coeffL1_X, coeffL1_C, one_mul]; exact hc 1
    calc F.q⁻¹ * coeffL1 (X 1 - MvPolynomial.C (F.c 0) - X 0 * MvPolynomial.C (F.c 1) :
          MvPolynomial (Fin 3) ℝ)
        ≤ Q * (1 + H + H) := mul_le_mul hqinv h1 (coeffL1_nonneg _) hQ0
      _ ≤ 3 * H * Q := by nlinarith
  have hU : coeffL1 F.UPoly ≤ 4 * H * Q := by
    unfold UPoly
    refine (coeffL1_C_mul_le _ _).trans ?_
    rw [abs_of_nonneg (inv_nonneg.mpr hqg.le)]
    have h1 : coeffL1 (X 2 - MvPolynomial.C (F.c 2) - X 0 * MvPolynomial.C (F.c 3) -
        MvPolynomial.C (F.c 4) * X 1 : MvPolynomial (Fin 3) ℝ) ≤ 1 + H + H + H := by
      refine (coeffL1_sub_le _ _).trans (add_le_add ((coeffL1_sub_le _ _).trans
        (add_le_add ((coeffL1_sub_le _ _).trans ?_) ?_)) ?_)
      · rw [coeffL1_X, coeffL1_C]; linarith [hc 2]
      · refine (coeffL1_mul_le _ _).trans ?_
        rw [coeffL1_X, coeffL1_C, one_mul]; exact hc 3
      · refine (coeffL1_mul_le _ _).trans ?_
        rw [coeffL1_X, coeffL1_C, mul_one]; exact hc 4
    calc Q * coeffL1 (X 2 - MvPolynomial.C (F.c 2) - X 0 * MvPolynomial.C (F.c 3) -
          MvPolynomial.C (F.c 4) * X 1 : MvPolynomial (Fin 3) ℝ)
        ≤ Q * (1 + H + H + H) := mul_le_mul_of_nonneg_left h1 hQ0
      _ ≤ 4 * H * Q := by nlinarith
  have hfit : coeffL1 F.fitPoly ≤ 4 * H := by
    unfold fitPoly
    have hm : ∀ (i : Fin 4) (j : Fin 3),
        coeffL1 (MvPolynomial.C (F.L i) * X j : MvPolynomial (Fin 3) ℝ) ≤ H := by
      intro i j
      refine (coeffL1_mul_le _ _).trans ?_
      rw [coeffL1_X, coeffL1_C, mul_one]; exact hL i
    refine (coeffL1_add_le _ _).trans ?_
    refine (add_le_add ((coeffL1_add_le _ _).trans (add_le_add ((coeffL1_add_le _ _).trans
      (add_le_add ((coeffL1_C (F.L 0)).trans_le (hL 0)) (hm 1 0))) (hm 2 1))) (hm 3 2)).trans ?_
    linarith
  have hα : coeffL1 (MvPolynomial.C (F.C 0) + MvPolynomial.C (F.C 1) * F.ztPoly +
      MvPolynomial.C (F.C 2) * F.zZPoly) ≤ 6 * H ^ 2 * Q := by
    refine (coeffL1_add_le _ _).trans ?_
    refine (add_le_add ((coeffL1_add_le _ _).trans (add_le_add ((coeffL1_C (F.C 0)).trans_le (hC 0))
      ((coeffL1_C_mul_le _ _).trans (mul_le_mul (hC 1) hzt (coeffL1_nonneg _) hH0))))
      ((coeffL1_C_mul_le _ _).trans (mul_le_mul (hC 2) hzZ (coeffL1_nonneg _) hH0))).trans ?_
    nlinarith
  have hPnc : coeffL1 F.PncPoly ≤ 40 * H ^ 3 * Q ^ 2 := by
    unfold PncPoly
    refine (coeffL1_add_le _ _).trans ?_
    have h1 := (coeffL1_mul_le (MvPolynomial.C (F.C 0) + MvPolynomial.C (F.C 1) * F.ztPoly +
      MvPolynomial.C (F.C 2) * F.zZPoly) F.UPoly).trans
        (mul_le_mul hα hU (coeffL1_nonneg _) (by positivity))
    have h2 : coeffL1 (MvPolynomial.C (F.C 3) * F.UPoly ^ 2) ≤ H * (4 * H * Q) ^ 2 := by
      refine (coeffL1_C_mul_le _ _).trans (mul_le_mul (hC 3) ?_ (coeffL1_nonneg _) hH0)
      exact (coeffL1_pow_le _ _).trans (pow_le_pow_left₀ (coeffL1_nonneg _) hU 2)
    nlinarith
  have hbind : coeffL1 (bind₁ F.cellSubst P) ≤ 9 * H ^ 3 * Q ^ 2 := by
    have hS : 1 ≤ 3 * H * Q := by nlinarith
    have hsub : ∀ i, coeffL1 (F.cellSubst i) ≤ 3 * H * Q := by
      intro i; fin_cases i
      · simp only [cellSubst]; exact hzt.trans (by nlinarith)
      · simp only [cellSubst]; exact hzZ
    refine (coeffL1_bind₁_le _ _ hS hsub P).trans ?_
    calc coeffL1 P * (3 * H * Q) ^ P.totalDegree ≤ H * (3 * H * Q) ^ 2 :=
          mul_le_mul hP (pow_le_pow_right₀ hS hPdeg) (by positivity) hH0
      _ = 9 * H ^ 3 * Q ^ 2 := by ring
  unfold cellGraph
  refine (coeffL1_add_le _ _).trans ?_
  have h3 : coeffL1 (MvPolynomial.C F.a * (F.PncPoly + bind₁ F.cellSubst P)) ≤
      1 * (40 * H ^ 3 * Q ^ 2 + 9 * H ^ 3 * Q ^ 2) := by
    refine (coeffL1_C_mul_le _ _).trans (mul_le_mul ?_ ((coeffL1_add_le _ _).trans
      (add_le_add hPnc hbind)) (coeffL1_nonneg _) zero_le_one)
    rw [abs_of_pos ha]; exact ha1
  have h4 : 4 * H ≤ 4 * H ^ 3 * Q ^ 2 := by
    have : H ≤ H ^ 3 := by nlinarith
    have : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
    nlinarith
  linarith

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
