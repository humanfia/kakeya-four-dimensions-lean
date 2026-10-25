-- Adapted from this LOT tree, o173, session x0581 (with x0598), commit 583cb89a,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/NormalizedSheetChoice.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.QuadraticSheetChoice
import Submission.Obl.k4_clean_cover_graph_atlas.PacketCoords

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4QuadraticSheets

noncomputable def selectedSheetTest (flat : Bool) (P : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 4) ℝ := if flat then pderiv 3 P else P

theorem eval_selectedSheetTest (flat : Bool) {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (u : Real3) (w : ℝ) :
    eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (selectedSheetTest flat P) =
      quadraticSheetValue flat (qc P / 2) (qbPoly P) (qcPoly P) u w := by
  cases flat
  · simpa only [selectedSheetTest, quadraticSheetValue, Bool.coe_false, ite_false] using
      eval_snoc_quadratic' hP (fun j => u j) w
  · simp only [selectedSheetTest, quadraticSheetValue, Bool.coe_true, ite_true]
    rw [eval_snoc_pderiv' hP]

theorem eval_selectedSheetSlope (flat : Bool) {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (u : Real3) (w : ℝ) :
    eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P)) =
      quadraticSheetSlope flat (qc P / 2) (qbPoly P) u w := by
  cases flat
  · simp only [selectedSheetTest, quadraticSheetSlope, Bool.coe_false, ite_false]
    rw [eval_snoc_pderiv' hP]
  · simp only [selectedSheetTest, quadraticSheetSlope, Bool.coe_true, ite_true]
    change eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ)
      (pderiv (Fin.last 3) (pderiv (Fin.last 3) P)) = 2 * (qc P / 2)
    rw [eval_pderiv2_eq_qc P hP]
    ring

theorem eval_originalSheetSlope {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (u : Real3) (w : ℝ) :
    eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 P) =
      2 * (qc P / 2) * w + eval (fun j => u j) (qbPoly P) := by
  simpa only [selectedSheetTest, quadraticSheetSlope, Bool.coe_false, ite_false] using
    eval_selectedSheetSlope false hP u w

/-- The common-coordinate sheet choice applied directly to a normalized test.
Its selected equation is either that test or its affine hidden derivative. -/
theorem exists_normalized_comparison_sheet_classified (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit : ℝ), 2 ≤ A → 0 < a_fit →
      ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
      (∀ e, |(qbPoly P * qbPoly P - MvPolynomial.C (2 * qc P) * qcPoly P).coeff e| ≤ A) →
      ∀ (u0 v0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        ‖v0 - u0‖ ≤ A ^ (-(C : ℝ)) / 16 →
        |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) P| ≤ a_fit * A →
        4 * A ^ (-1 : ℝ) ≤ |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| →
        |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| ≤ A →
      ∃ (flat : Bool) (F : RealSheet 2),
        (flat = false ↔ |qc P / 2| * a_fit ≤ A ^ (-20 : ℝ)) ∧
        let σ := eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))
        0 < |σ| ∧ ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := v0 + (A ^ (-(C : ℝ)) / 128) • x
          let w := (F.f (emb x)).re
          eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (selectedSheetTest flat P) = 0 ∧
          19 / 20 * |σ| ≤ |eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))| ∧
          |eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))| ≤ 21 / 20 * |σ| ∧
          0 < eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P)) * σ ∧
          ∀ v : ℝ, |eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) P| ≤ a_fit * A →
            |eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) (pderiv 3 P)| ≤ A →
            (flat = false → 0 < eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) (pderiv 3 P) *
              eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)) →
            |v - w| ≤ a_fit * A ^ ((C : ℝ) + 2) := by
  obtain ⟨C, hC, hchoose⟩ := exists_quadratic_comparison_sheet_classified h
  refine ⟨C, hC, ?_⟩
  intro A a_fit hA ha_fit P hP hcoeff u0 v0 w0 hu0 hv0 hvalue hslo hshi
  have hcoeff' : ∀ e,
      |(qbPoly P * qbPoly P - MvPolynomial.C (4 * (qc P / 2)) * qcPoly P).coeff e| ≤ A := by
    simpa only [show 4 * (qc P / 2) = 2 * qc P by ring] using hcoeff
  rw [eval_snoc_quadratic' hP] at hvalue
  rw [eval_originalSheetSlope hP] at hslo hshi
  obtain ⟨flat, F, hclass, hF⟩ := hchoose A a_fit (qc P / 2) hA ha_fit (qbPoly P) (qcPoly P)
    (totalDegree_qbPoly_le hP) (totalDegree_qcPoly_le hP) hcoeff' u0 v0 w0 hu0 hv0 hvalue hslo hshi
  refine ⟨flat, F, hclass, ?_⟩
  simpa only [eval_selectedSheetTest flat hP, eval_selectedSheetSlope flat hP,
    eval_snoc_quadratic' hP, eval_originalSheetSlope hP, quadraticSheetSlope] using hF

theorem exists_normalized_comparison_sheet (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit : ℝ), 2 ≤ A → 0 < a_fit →
      ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
      (∀ e, |(qbPoly P * qbPoly P - MvPolynomial.C (2 * qc P) * qcPoly P).coeff e| ≤ A) →
      ∀ (u0 v0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        ‖v0 - u0‖ ≤ A ^ (-(C : ℝ)) / 16 →
        |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) P| ≤ a_fit * A →
        4 * A ^ (-1 : ℝ) ≤ |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| →
        |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| ≤ A →
      ∃ (flat : Bool) (F : RealSheet 2),
        let σ := eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))
        0 < |σ| ∧ ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := v0 + (A ^ (-(C : ℝ)) / 128) • x
          let w := (F.f (emb x)).re
          eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (selectedSheetTest flat P) = 0 ∧
          19 / 20 * |σ| ≤ |eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))| ∧
          |eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))| ≤ 21 / 20 * |σ| ∧
          0 < eval (Fin.snoc (fun j => u j) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P)) * σ ∧
          ∀ v : ℝ, |eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) P| ≤ a_fit * A →
            |eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) (pderiv 3 P)| ≤ A →
            (flat = false → 0 < eval (Fin.snoc (fun j => u j) v : Fin 4 → ℝ) (pderiv 3 P) *
              eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)) →
            |v - w| ≤ a_fit * A ^ ((C : ℝ) + 2) := by
  obtain ⟨C, hC, hchoose⟩ := exists_normalized_comparison_sheet_classified h
  refine ⟨C, hC, ?_⟩
  intro A a_fit hA ha_fit P hP hcoeff u0 v0 w0 hu0 hv0 hvalue hslo hshi
  obtain ⟨flat, F, _, hF⟩ := hchoose A a_fit hA ha_fit P hP hcoeff
    u0 v0 w0 hu0 hv0 hvalue hslo hshi
  exact ⟨flat, F, hF⟩

end Submission.Obl.k4_clean_cover_graph_atlas
