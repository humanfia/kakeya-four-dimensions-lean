-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PacketCoords.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Frames
import Submission.Obl.k4_clean_cover_graph_atlas.RepTests
import Submission.Obl.k4_clean_cover_graph_atlas.Tests

/-!
# Normalized packet coordinates

An old chart with time resolution `T`, block `j`, centre `c`, velocity `u`, frame `Q` and world
scale `B` has normalized coordinates `(s, z, w̃)`:
`s = 2^T t - j`, `z = Q⁻¹ (y - c - t u)`, `w̃ = B w`. `packetSubst` writes the original coordinates
as affine polynomials in the normalized ones, `normPoly R` is a test in normalized coordinates and
`normPt l t` is the normalized point of a line (`eval_normPoly_normPt`). The hidden quadratic of a
normalized test is `qa P w̃² + qbPoly P (u) w̃ + qcPoly P (u)` with `qbPoly`, `qcPoly` polynomials in
the three base coordinates (`eval_snoc_quadratic'`), of degrees at most one and two.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The original coordinates as affine polynomials in the normalized coordinates. -/
noncomputable def packetSubst (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C ((j : ℝ) / 2 ^ T) + C (1 / 2 ^ T) * X 0,
    C (c 0 + (j : ℝ) / 2 ^ T * u 0) + C (1 / 2 ^ T * u 0) * X 0 + C (Q 0 0) * X 1 + C (Q 0 1) * X 2,
    C (c 1 + (j : ℝ) / 2 ^ T * u 1) + C (1 / 2 ^ T * u 1) * X 0 + C (Q 1 0) * X 1 + C (Q 1 1) * X 2,
    C B⁻¹ * X 3]

/-- A test in normalized coordinates. -/
noncomputable def normPoly (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  eval₂ C (packetSubst T j c u Q B) R

/-- The normalized point of a line at a time. -/
noncomputable def normPt (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  ![2 ^ T * t - j, (zc Q c u l t) 0, (zc Q c u l t) 1, B * gx l t 3]

theorem eval_normPoly (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    eval v (normPoly T j c u Q B R) = eval (fun i => eval v (packetSubst T j c u Q B i)) R := by
  rw [normPoly, eval_eval₂]
  simp only [MvPolynomial.eval]
  congr 1
  ext r
  simp

/-- The substitution maps the normalized point of a line back to the line point. -/
theorem packetSubst_normPt {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : B ≠ 0)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun i => eval (normPt T j c u Q B l t) (packetSubst T j c u Q B i)) = gx l t := by
  have h2 : (2 : ℝ) ^ T ≠ 0 := by positivity
  set z := zc Q c u l t with hzdef
  have hz := toEuclideanLin_inv_cancel Q hQ (gy l t - c - t • u)
  have hz' : ∀ e : Fin 2, Q e 0 * z 0 + Q e 1 * z 1 = (gy l t) e - c e - t * u e := by
    intro e
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v e) hz
    simp only [toEuclideanLin_apply_fin2] at this
    simp only [hzdef, zc, toEuclideanLin_apply_fin2] at this ⊢
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this
  have hgy0 : (gy l t) 0 = gx l t 1 := by simp [gy]
  have hgy1 : (gy l t) 1 = gx l t 2 := by simp [gy]
  have e0 : eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 0) =
      (j : ℝ) / 2 ^ T + 1 / 2 ^ T * (2 ^ T * t - j) := by
    simp [packetSubst, normPt]
  have e1 : eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 1) =
      c 0 + (j : ℝ) / 2 ^ T * u 0 + 1 / 2 ^ T * u 0 * (2 ^ T * t - j) + Q 0 0 * z 0 +
        Q 0 1 * z 1 := by
    simp [packetSubst, normPt, hzdef]
  have e2 : eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 2) =
      c 1 + (j : ℝ) / 2 ^ T * u 1 + 1 / 2 ^ T * u 1 * (2 ^ T * t - j) + Q 1 0 * z 0 +
        Q 1 1 * z 1 := by
    simp [packetSubst, normPt, hzdef]
  have e3 : eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 3) = B⁻¹ * (B * gx l t 3) := by
    simp [packetSubst, normPt]
  funext i
  fin_cases i
  · change eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 0) = gx l t 0
    rw [e0]
    have : gx l t 0 = t := by simp [gx]
    rw [this]
    field_simp
    ring
  · change eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 1) = gx l t 1
    rw [e1]
    have h := hz' 0
    rw [hgy0] at h
    have h' : (j : ℝ) / 2 ^ T * u 0 + 1 / 2 ^ T * u 0 * (2 ^ T * t - j) = t * u 0 := by
      field_simp; ring
    linarith
  · change eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 2) = gx l t 2
    rw [e2]
    have h := hz' 1
    rw [hgy1] at h
    have h' : (j : ℝ) / 2 ^ T * u 1 + 1 / 2 ^ T * u 1 * (2 ^ T * t - j) = t * u 1 := by
      field_simp; ring
    linarith
  · change eval (normPt T j c u Q B l t) (packetSubst T j c u Q B 3) = gx l t 3
    rw [e3]
    field_simp

theorem eval_normPoly_normPt {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : B ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (normPt T j c u Q B l t) (normPoly T j c u Q B R) = eval (gx l t) R := by
  rw [eval_normPoly, packetSubst_normPt hQ hB]

section Hidden

/-- The base part of the substitution, at hidden value `w̃`. -/
theorem packetSubst_snoc (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (z : Fin 3 → ℝ) (w : ℝ) :
    (fun i => eval (Fin.snoc z w : Fin 4 → ℝ) (packetSubst T j c u Q B i)) =
      Fin.snoc (fun i : Fin 3 => eval (Fin.snoc z 0 : Fin 4 → ℝ) (packetSubst T j c u Q B i.castSucc))
        (B⁻¹ * w) := by
  funext i
  fin_cases i <;> simp [packetSubst, Fin.snoc]

/-- The hidden derivative of a normalized test is the original hidden derivative divided by `B`. -/
theorem eval_pderiv_normPoly (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    eval v (pderiv 3 (normPoly T j c u Q B R)) =
      B⁻¹ * eval (fun i => eval v (packetSubst T j c u Q B i)) (pderiv 3 R) := by
  set z := Fin.init v
  have hv : v = (Fin.snoc z (v 3) : Fin 4 → ℝ) := (snoc_init_eq v).symm
  set z' : Fin 3 → ℝ := fun i => eval (Fin.snoc z 0 : Fin 4 → ℝ) (packetSubst T j c u Q B i.castSucc)
  have hφ : ∀ w : ℝ, eval (Fin.snoc z w : Fin 4 → ℝ) (normPoly T j c u Q B R) =
      eval (Fin.snoc z' (B⁻¹ * w) : Fin 4 → ℝ) R := by
    intro w
    rw [eval_normPoly, packetSubst_snoc]
  have hd1 := hasDerivAt_eval_snoc (n := 3) (normPoly T j c u Q B R) z (v 3)
  have hd2 : HasDerivAt (fun w : ℝ => eval (Fin.snoc z' (B⁻¹ * w) : Fin 4 → ℝ) R)
      (eval (Fin.snoc z' (B⁻¹ * v 3) : Fin 4 → ℝ) (pderiv (Fin.last 3) R) * B⁻¹) (v 3) := by
    have h := hasDerivAt_eval_snoc (n := 3) R z' (B⁻¹ * v 3)
    have hl : HasDerivAt (fun w : ℝ => B⁻¹ * w) B⁻¹ (v 3) := by
      simpa using (hasDerivAt_id (v 3)).const_mul B⁻¹
    exact h.comp (v 3) hl
  have heq : (fun w => eval (Fin.snoc z w : Fin 4 → ℝ) (normPoly T j c u Q B R)) =
      fun w => eval (Fin.snoc z' (B⁻¹ * w) : Fin 4 → ℝ) R := funext hφ
  rw [heq] at hd1
  have huniq := hd1.unique hd2
  conv_lhs => rw [hv]
  change eval (Fin.snoc z (v 3) : Fin 4 → ℝ) (pderiv (Fin.last 3) (normPoly T j c u Q B R)) = _
  rw [huniq]
  have hsub : (fun i => eval v (packetSubst T j c u Q B i)) =
      (Fin.snoc z' (B⁻¹ * v 3) : Fin 4 → ℝ) := by
    conv_lhs => rw [hv]
    exact packetSubst_snoc T j c u Q B z (v 3)
  rw [hsub]
  change _ = B⁻¹ * eval (Fin.snoc z' (B⁻¹ * v 3) : Fin 4 → ℝ) (pderiv (Fin.last 3) R)
  ring

/-- The base coefficient polynomials of a quadratic test (hidden variable last). -/
noncomputable def baseSubst : Fin 4 → MvPolynomial (Fin 3) ℝ := Fin.snoc X 0

noncomputable def qbPoly (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  eval₂ C baseSubst (pderiv 3 P)

noncomputable def qcPoly (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  eval₂ C baseSubst P

theorem baseSubst_last : baseSubst (Fin.last 3) = 0 :=
  Fin.snoc_last (α := fun _ => MvPolynomial (Fin 3) ℝ) (p := X) (x := 0)

theorem baseSubst_castSucc (i : Fin 3) : baseSubst i.castSucc = X i := by
  simp [baseSubst]

theorem eval_baseSubst_eval₂ (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) :
    eval z (eval₂ C baseSubst P) = eval (Fin.snoc z 0 : Fin 4 → ℝ) P := by
  rw [eval_eval₂]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r; simp
  · funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [baseSubst_last, map_zero]
      exact (Fin.snoc_last (α := fun _ => ℝ) (p := z) (x := 0)).symm
    · rw [baseSubst_castSucc]
      change eval z (X i) = _
      rw [eval_X]
      exact (Fin.snoc_castSucc (α := fun _ => ℝ) (p := z) (x := 0) i).symm

theorem eval_qbPoly (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) :
    eval z (qbPoly P) = qb P z := by
  rw [qbPoly, eval_baseSubst_eval₂]; rfl

theorem eval_qcPoly (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) :
    eval z (qcPoly P) = qg P z := by
  rw [qcPoly, eval_baseSubst_eval₂]; rfl

theorem totalDegree_baseSubst_le (i : Fin 4) : (baseSubst i).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [baseSubst_last]; simp
  · rw [baseSubst_castSucc]; simp [totalDegree_X]

theorem totalDegree_qbPoly_le {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) :
    (qbPoly P).totalDegree ≤ 1 := by
  have h := totalDegree_eval₂C_le baseSubst (s := 1) totalDegree_baseSubst_le (pderiv 3 P)
  have h1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
  simp only [one_mul] at h
  exact h.trans h1

theorem totalDegree_qcPoly_le {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) :
    (qcPoly P).totalDegree ≤ 2 := by
  have h := totalDegree_eval₂C_le baseSubst (s := 1) totalDegree_baseSubst_le P
  simp only [one_mul] at h
  exact h.trans hP

/-- The hidden quadratic with polynomial base coefficients. -/
theorem eval_snoc_quadratic' {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w : Fin 4 → ℝ) P =
      qc P / 2 * w ^ 2 + eval z (qbPoly P) * w + eval z (qcPoly P) := by
  rw [eval_qbPoly, eval_qcPoly, eval_snoc_quadratic (n := 3) P hP]
  ring

theorem eval_snoc_pderiv' {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv 3 P) = 2 * (qc P / 2) * w + eval z (qbPoly P) := by
  rw [eval_qbPoly]
  have := eval_snoc_pderiv (n := 3) P hP z w
  change eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (Fin.last 3) P) = _
  rw [this]
  ring

end Hidden

section Transfer

/-- The hidden derivative of a normalized test is the normalized hidden derivative over `B`. -/
theorem pderiv_normPoly (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    pderiv 3 (normPoly T j c u Q B R) = C B⁻¹ * normPoly T j c u Q B (pderiv 3 R) := by
  apply MvPolynomial.funext
  intro v
  rw [eval_pderiv_normPoly, map_mul, eval_C, eval_normPoly]

theorem qc_normPoly {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} {R : MvPolynomial (Fin 4) ℝ} (hR : R.totalDegree ≤ 2) :
    qc (normPoly T j c u Q B R) = B⁻¹ * B⁻¹ * qc R := by
  unfold qc
  change eval 0 (pderiv 3 (pderiv 3 (normPoly T j c u Q B R))) =
    B⁻¹ * B⁻¹ * eval 0 (pderiv 3 (pderiv 3 R))
  rw [pderiv_normPoly, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul,
    pderiv_normPoly, map_mul, map_mul, eval_C]
  rw [eval_normPoly, eval_pderiv_pderiv_const hR _ 0]
  ring

/-- Test values, hidden derivatives and curvatures along a line in normalized coordinates. -/
theorem normPt_tests {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : B ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (normPt T j c u Q B l t) (normPoly T j c u Q B R) = eval (gx l t) R ∧
      eval (normPt T j c u Q B l t) (pderiv 3 (normPoly T j c u Q B R)) =
        B⁻¹ * eval (gx l t) (pderiv 3 R) := by
  refine ⟨eval_normPoly_normPt hQ hB R l t, ?_⟩
  rw [eval_pderiv_normPoly, packetSubst_normPt hQ hB]

end Transfer

end Submission.Obl.k4_clean_cover_graph_atlas
