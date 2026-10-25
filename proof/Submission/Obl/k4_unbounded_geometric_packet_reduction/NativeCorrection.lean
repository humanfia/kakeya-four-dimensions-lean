import Submission.Lib.K4XInterface.Charts

/-!
The elementary polynomial identities are adapted from this LOT tree, o120,
session x0402, `NativeCorrection.lean`, commit
`b6c9f0c78a897e02a6543f9fe1234d43a2ee16c7`.
The chart lemma records how a scalar predictor returns to the original native test.
-/

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MvPolynomial
open Submission.Lib.K4XInterface

noncomputable section

def nativeCorrection (P : MvPolynomial (Fin 4) ℝ) (F : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 4) ℝ := P - rename Fin.castSucc F

theorem pderiv_base_rename (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (rename Fin.castSucc F) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hj⟩ := mem_vars_rename Fin.castSucc F h
  have hjv := congrArg Fin.val hj
  have := j.isLt
  change j.val = 3 at hjv
  omega

theorem nativeCorrection_pderiv (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (nativeCorrection P F) = pderiv (3 : Fin 4) P := by
  simp only [nativeCorrection, map_sub, pderiv_base_rename, sub_zero]

theorem nativeCorrection_pderiv_pderiv (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (nativeCorrection P F)) =
      pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P) := by
  rw [nativeCorrection_pderiv]

theorem eval_nativeCorrection (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) (z : Fin 4 → ℝ) :
    eval z (nativeCorrection P F) = eval z P - eval (z ∘ Fin.castSucc) F := by
  simp [nativeCorrection, eval_rename]

theorem nativeCorrection_degree {P : MvPolynomial (Fin 4) ℝ}
    {F : MvPolynomial (Fin 3) ℝ} (hP : P.totalDegree ≤ 2) (hF : F.totalDegree ≤ 2) :
    (nativeCorrection P F).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans
    (max_le hP ((totalDegree_rename_le Fin.castSucc F).trans hF))

/-- A fit in the base coordinates improves the test value at a deeper scale.
Both hidden derivative bounds and their incidence floor remain those of the
original chart.  No conditional measure replaces the original incidence law. -/
theorem gchart_nativeCorrection {N : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ}
    {j r r' B : ℝ} {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {P : MvPolynomial (Fin 4) ℝ} {F : MvPolynomial (Fin 3) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {I : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {ex : Prop} (hc : gchart N M D κ T j r B E c u Q P A I ex)
    (hF : F.totalDegree ≤ 2)
    (hcoeff : ∀ e, |(nativeCorrection P F).coeff e| ≤ N ^ M)
    (hδ : gδ N r' ≤ gδ N r)
    (hfit : ∀ l ∈ A, ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
      |eval (gx l t) P - eval (gx l t ∘ Fin.castSucc) F| ≤ κ * gδ N r') :
    gchart N M D κ T j r' B E c u Q (nativeCorrection P F) A I ex := by
  rcases hc with ⟨hQ, hcu, hQi, hQs, hP, hPc, hA, hI, hfmt, hlines, hpoints, hex⟩
  refine ⟨hQ, hcu, hQi, hQs, nativeCorrection_degree hP hF, hcoeff,
    hA, hI, hfmt, ?_, ?_, hex⟩
  · intro l hl
    obtain ⟨hi, hb, hline⟩ := hlines l hl
    refine ⟨hi, hb, fun t ht => ?_⟩
    obtain ⟨hgeom, hval, hder, hder2⟩ := hline t ht
    refine ⟨hgeom, ?_, ?_, ?_⟩
    · rw [eval_nativeCorrection]
      exact hfit l hl t ht
    · simpa only [nativeCorrection_pderiv] using hder
    · rw [nativeCorrection_pderiv_pderiv]
      exact hder2.trans (div_le_div_of_nonneg_left
        (by have := (norm_nonneg (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u))).trans hgeom
            positivity)
        (gδ_pos N r') hδ)
  · intro p hp
    simpa only [nativeCorrection_pderiv] using hpoints p hp

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
