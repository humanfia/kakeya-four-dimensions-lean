-- Adapted from this LOT tree, o173, session x0581 (with x0598), commit 583cb89a,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RepresentativeSelection.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.RootTestInclusion

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Set MvPolynomial Submission.Lib.K4QuadraticSheets

/-- A representative is tested at the actual matching error. Its threshold can then
be bounded above by the larger desired output threshold. The high-curvature alternative
is the affine center equation. -/
theorem representative_root_test_selection_bounded {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) {s η ta tb : ℝ} (hs : 0 < s) (hη : 0 < η)
    (pos : Bool) (S : Set (ℕ × (Fin 6 → ℝ)))
    (hfit : ∀ l ∈ S, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ∃ w : ℝ, eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) P = 0 ∧
        |(Submission.Lib.K4XInterface.gx l t) 3 - w| ≤ η ∧
        if pos then
          19 / 20 * s ≤ eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s
        else
          19 / 20 * s ≤ -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s) :
    ∃ (Q : MvPolynomial (Fin 4) ℝ) (sq m₀ : ℝ),
      (Q = P ∨ Q = pderiv 3 P) ∧ (sq = s ∨ sq = |qc P|) ∧ Q.totalDegree ≤ 2 ∧
      0 < sq ∧ 0 ≤ m₀ ∧ m₀ ≤ 85 * sq * η ∧ |qc Q| * m₀ ≤ sq ^ 2 / 40 ∧ s / (1 + 80 * η) ≤ sq ∧
      ∀ l ∈ S, l ∈ rootTestSet Q sq m₀ ta tb := by
  by_cases hlow : |qc P| * η ≤ s / 80
  · refine ⟨P, s, 2 * s * η, Or.inl rfl, Or.inl rfl, hP, hs, by positivity, ?_, ?_, ?_, ?_⟩
    · nlinarith [mul_pos hs hη]
    · nlinarith
    · apply (div_le_iff₀ (by positivity : 0 < 1 + 80 * η)).mpr
      nlinarith [mul_nonneg hs.le hη.le]
    · intro l hl
      exact (rootTestSet_of_near_roots hP hs hη.le hlow pos l (hfit l hl)).1
  · have hlarge : s / 80 < |qc P| * η := lt_of_not_ge hlow
    have hqcne : qc P ≠ 0 := by
      intro hz
      rw [hz, abs_zero, zero_mul] at hlarge
      linarith
    have hqcpos : 0 < |qc P| := abs_pos.mpr hqcne
    let Q := pderiv (3 : Fin 4) P
    have hQdegree : Q.totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
    have hQcurv : qc Q = 0 := by
      have h0 : (pderiv (3 : Fin 4) Q).totalDegree = 0 :=
        Nat.le_zero.mp (totalDegree_pderiv_le' Q (3 : Fin 4) hQdegree)
      have hzero : pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q) = 0 := by
        rw [eq_C_of_totalDegree_eq_zero _ h0, pderiv_C]
      simpa only [qc, last_three, hzero, map_zero] using congrArg (eval (0 : Fin 4 → ℝ)) hzero
    have hder (x : Fin 4 → ℝ) : eval x (pderiv (3 : Fin 4) Q) = qc P :=
      eval_pderiv2_eq_qc P hP x
    have hvalue (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ S) (t : ℝ)
        (ht : t = ta ∨ t = (ta + tb) / 2 ∨ t = tb) :
        |eval (Submission.Lib.K4XInterface.gx l t) Q| ≤ 85 * |qc P| * η := by
      obtain ⟨w, hroot, hclose, hwindow⟩ := hfit l hl t ht
      let x := Submission.Lib.K4XInterface.gx l t
      let g := eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)
      have hg : |g| ≤ 21 / 20 * s := by
        cases pos <;> simp only [Bool.coe_false, ite_false, ite_true] at hwindow
        · rw [abs_of_neg (by dsimp only [g, x]; linarith)]
          exact hwindow.2
        · rw [abs_of_pos (by dsimp only [g, x]; linarith)]
          exact hwindow.2
      have hx : x = (Fin.snoc (Fin.init x) (x 3) : Fin 4 → ℝ) := (snoc_init_eq x).symm
      have he : eval x Q = g + qc P * (x 3 - w) := by
        conv_lhs => rw [hx]
        exact eval_pderiv_expand hP _ _ _
      change |eval x Q| ≤ _
      rw [he]
      calc
        _ ≤ |g| + |qc P| * |x 3 - w| := by
          simpa only [abs_mul] using abs_add_le g (qc P * (x 3 - w))
        _ ≤ 21 / 20 * s + |qc P| * η := add_le_add hg
          (mul_le_mul_of_nonneg_left hclose (abs_nonneg _))
        _ ≤ _ := by nlinarith
    refine ⟨Q, |qc P|, 85 * |qc P| * η, Or.inr rfl, Or.inr rfl,
      hQdegree.trans (by norm_num), hqcpos, by positivity, le_rfl, ?_, ?_, ?_⟩
    · rw [hQcurv, abs_zero, zero_mul]
      positivity
    · apply (div_le_iff₀ (by positivity : 0 < 1 + 80 * η)).mpr
      nlinarith
    · intro l hl
      refine ⟨hvalue l hl ta (Or.inl rfl),
        hvalue l hl ((ta + tb) / 2) (Or.inr (Or.inl rfl)),
        hvalue l hl tb (Or.inr (Or.inr rfl)), ?_⟩
      by_cases hqc0 : 0 ≤ qc P
      · apply Or.inl
        simp only [hder, abs_of_nonneg hqc0]
        exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
      · apply Or.inr
        simp only [hder, abs_of_neg (not_le.mp hqc0)]
        exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem representative_root_test_selection {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) {s η ta tb : ℝ} (hs : 0 < s) (hη : 0 < η)
    (pos : Bool) (S : Set (ℕ × (Fin 6 → ℝ)))
    (hfit : ∀ l ∈ S, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ∃ w : ℝ, eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) P = 0 ∧
        |(Submission.Lib.K4XInterface.gx l t) 3 - w| ≤ η ∧
        if pos then
          19 / 20 * s ≤ eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s
        else
          19 / 20 * s ≤ -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s) :
    ∃ (Q : MvPolynomial (Fin 4) ℝ) (sq m₀ : ℝ),
      (Q = P ∨ Q = pderiv 3 P) ∧ (sq = s ∨ sq = |qc P|) ∧ Q.totalDegree ≤ 2 ∧
      0 < sq ∧ 0 ≤ m₀ ∧ m₀ ≤ 85 * sq * η ∧ |qc Q| * m₀ ≤ sq ^ 2 / 40 ∧
      ∀ l ∈ S, l ∈ rootTestSet Q sq m₀ ta tb := by
  obtain ⟨Q, sq, m₀, hQ, hschoice, hdegree, hsq, hm₀, hbound, hcurv, _, hmem⟩ :=
    representative_root_test_selection_bounded hP hs hη pos S hfit
  exact ⟨Q, sq, m₀, hQ, hschoice, hdegree, hsq, hm₀, hbound, hcurv, hmem⟩

end Submission.Obl.k4_clean_cover_graph_atlas
