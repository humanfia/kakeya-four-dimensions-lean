-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/BranchFitting.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/BranchFitting.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.NormalizedSheetChoice
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SourceFloor

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MvPolynomial Submission.Lib.K4QuadraticSheets

noncomputable def comparisonCurvePoint (centre : Real3) (radius : ℝ)
    (base : Real3) (hidden : ℝ) : Fin 4 → ℝ :=
  Fin.snoc (fun j => (centre + radius • base) j) hidden

/-- The exact root and narrow derivative data of a sheet in the common base. -/
def NormalizedRootCertificate (P : MvPolynomial (Fin 4) ℝ) (flat : Bool) (F : RealSheet 2)
    (centre : Real3) (radius σ : ℝ) : Prop :=
  0 < |σ| ∧ ∀ x : Real3, ‖x‖ ≤ 1 →
    let v := comparisonCurvePoint centre radius x (F.f (emb x)).re
    eval v (selectedSheetTest flat P) = 0 ∧
      19 / 20 * |σ| ≤ |eval v (pderiv 3 (selectedSheetTest flat P))| ∧
      |eval v (pderiv 3 (selectedSheetTest flat P))| ≤ 21 / 20 * |σ| ∧
      0 < eval v (pderiv 3 (selectedSheetTest flat P)) * σ

private theorem curve_same_sign {g : ℝ → ℝ} (hg : Continuous g) {ta tb t u : ℝ}
    (ht : t ∈ Icc ta tb) (hu : u ∈ Icc ta tb)
    (hnz : ∀ v ∈ Icc ta tb, g v ≠ 0) : 0 < g t * g u := by
  have hsign := Submission.Obl.k4_scalar_sign_choice.sign_eq_of_nonzero_interval hg
    (fun v hv => hnz v (uIcc_subset_Icc ht hu hv))
  rcases lt_or_gt_of_ne (hnz t ht) with hneg | hpos
  · have huneg : g u < 0 := sign_eq_neg_one_iff.mp (hsign.symm.trans (sign_neg hneg))
    exact mul_pos_of_neg_of_neg hneg huneg
  · have hupos : 0 < g u := sign_eq_one_iff.mp (hsign.symm.trans (sign_pos hpos))
    exact mul_pos hpos hupos

/-- A whole family of curves with one midpoint sign bit fits a common comparison
sheet. Low-curvature source derivatives are proved nonzero before the branch sign
is used. The affine case needs no sign argument. -/
theorem exists_comparison_sheet_for_curves (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit : ℝ), 2 ≤ A → 0 < a_fit →
      ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
      (∀ e, |(qbPoly P * qbPoly P - MvPolynomial.C (2 * qc P) * qcPoly P).coeff e| ≤ A) →
      ∀ {Z : Type*} (centre : Real3) (base : Z → ℝ → Real3) (hidden : Z → ℝ → ℝ)
        (z0 : Z) (ta tb t0 : ℝ), ta ≤ tb → t0 ∈ Icc ta tb →
      (∀ z t, t ∈ Icc ta tb → ‖base z t‖ ≤ (1 : ℝ) / 2) →
      ‖centre + (A ^ (-(C : ℝ)) / 128) • base z0 t0‖ ≤ A →
      (∀ z t, t ∈ Icc ta tb →
        |eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128) (base z t) (hidden z t)) P| ≤ a_fit * A) →
      (∀ z t, t ∈ Icc ta tb →
        |eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128) (base z t) (hidden z t)) (pderiv 3 P)| ≤ A) →
      4 * A ^ (-1 : ℝ) ≤
        |eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128) (base z0 t0) (hidden z0 t0)) (pderiv 3 P)| →
      (∀ z, Continuous (fun t =>
        eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128) (base z t) (hidden z t)) (pderiv 3 P))) →
      (∀ z, decide (0 ≤ eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128)
          (base z ((ta + tb) / 2)) (hidden z ((ta + tb) / 2))) (pderiv 3 P)) =
        decide (0 ≤ eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128)
          (base z0 ((ta + tb) / 2)) (hidden z0 ((ta + tb) / 2))) (pderiv 3 P))) →
      ∃ (flat : Bool) (F : RealSheet 2),
        (flat = false ↔ |qc P / 2| * a_fit ≤ A ^ (-20 : ℝ)) ∧
        let σ := eval (comparisonCurvePoint centre (A ^ (-(C : ℝ)) / 128)
          (base z0 t0) (hidden z0 t0)) (pderiv 3 (selectedSheetTest flat P))
        NormalizedRootCertificate P flat F centre (A ^ (-(C : ℝ)) / 128) σ ∧
          ∀ z t, t ∈ Icc ta tb →
            |hidden z t - (F.f (emb (base z t))).re| ≤ a_fit * A ^ ((C : ℝ) + 2) := by
  obtain ⟨C, hC, hchoose⟩ := exists_normalized_comparison_sheet_classified h
  refine ⟨C, hC, ?_⟩
  intro A a_fit hA ha_fit P hP hcoeff Z centre base hidden z0 ta tb t0 hab ht0
    hhalf hanchor hvalue hupper hregular hcont hbit
  let radius := A ^ (-(C : ℝ)) / 128
  let u0 := centre + radius • base z0 t0
  let w0 := hidden z0 t0
  have hApos : 0 < A := by linarith
  have hradius : 0 < radius := by dsimp only [radius]; positivity
  have hcentre : ‖centre - u0‖ ≤ A ^ (-(C : ℝ)) / 16 := by
    calc
      _ = ‖radius • base z0 t0‖ := by dsimp only [u0]; rw [norm_sub_rev, add_sub_cancel_left]
      _ = radius * ‖base z0 t0‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hradius]
      _ ≤ radius * (1 / 2) := mul_le_mul_of_nonneg_left (hhalf z0 t0 ht0) hradius.le
      _ ≤ _ := by dsimp only [radius]; nlinarith [Real.rpow_nonneg hApos.le (-(C : ℝ))]
  obtain ⟨flat, F, hclass, hσ, hF⟩ := hchoose A a_fit hA ha_fit P hP hcoeff
    u0 centre w0 hanchor hcentre (hvalue z0 t0 ht0) hregular (hupper z0 t0 ht0)
  refine ⟨flat, F, hclass, ?_, ?_⟩
  · exact ⟨hσ, fun x hx => ⟨(hF x hx).1, (hF x hx).2.1,
      (hF x hx).2.2.1, (hF x hx).2.2.2.1⟩⟩
  · intro z t ht
    have hunit : ‖base z t‖ ≤ 1 := (hhalf z t ht).trans (by norm_num)
    apply (hF (base z t) hunit).2.2.2.2 (hidden z t) (hvalue z t ht) (hupper z t ht)
    intro hflat
    have hsmall := hclass.mp hflat
    have htest : selectedSheetTest flat P = P := by
      simp only [selectedSheetTest, hflat, Bool.coe_false, ite_false]
    have hnz : ∀ y v, v ∈ Icc ta tb →
        eval (comparisonCurvePoint centre radius (base y v) (hidden y v)) (pderiv 3 P) ≠ 0 := by
      intro y v hv
      have hnorm : ‖base y v‖ ≤ 1 := (hhalf y v hv).trans (by norm_num)
      obtain ⟨hroot, hlo, _, _, _⟩ := hF (base y v) hnorm
      have hroot' : eval (Fin.snoc
          (Fin.init (comparisonCurvePoint centre radius (base y v) (hidden y v)))
          (F.f (emb (base y v))).re : Fin 4 → ℝ) P = 0 := by
        simpa only [comparisonCurvePoint, Fin.init_snoc, htest] using hroot
      have hlo' : 19 / 20 * |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| ≤
          |eval (Fin.snoc
            (Fin.init (comparisonCurvePoint centre radius (base y v) (hidden y v)))
            (F.f (emb (base y v))).re : Fin 4 → ℝ) (pderiv 3 P)| := by
        simpa only [comparisonCurvePoint, Fin.init_snoc, htest] using hlo
      have hder : A ^ (-1 : ℝ) ≤
          |eval (Fin.snoc
            (Fin.init (comparisonCurvePoint centre radius (base y v) (hidden y v)))
            (F.f (emb (base y v))).re : Fin 4 → ℝ) (pderiv 3 P)| := by
        have hreg : 4 * A ^ (-1 : ℝ) ≤
            |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| := hregular
        nlinarith [Real.rpow_nonneg hApos.le (-1 : ℝ)]
      exact low_curvature_source_nonzero hP hA hsmall _ _ hroot' hder (hvalue y v hv)
    have hmid : (ta + tb) / 2 ∈ Icc ta tb := ⟨by linarith, by linarith⟩
    have hleft := sign_bits_eq_of_mul_pos (curve_same_sign (hcont z) ht hmid (hnz z))
    have hright := sign_bits_eq_of_mul_pos (curve_same_sign (hcont z0) hmid ht0 (hnz z0))
    exact mul_pos_of_equal_sign_bits (hnz z t ht) (hnz z0 t0 ht0)
      (hleft.trans ((hbit z).trans hright))

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
