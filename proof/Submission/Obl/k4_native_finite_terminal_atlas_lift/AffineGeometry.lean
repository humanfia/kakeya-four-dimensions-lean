/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/AffineGeometry.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Definitions
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MeasureTheory MvPolynomial

/-- Native coefficient normalization from physical to unit block coordinates.
The hidden spatial coordinate remains affine in the rescaled time. -/
noncomputable def normalizedCoefficients (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (a : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![V 0 0 * (a 0 + t₀ * a 3 - c 0 - t₀ * u 0) +
      V 0 1 * (a 1 + t₀ * a 4 - c 1 - t₀ * u 1),
    V 1 0 * (a 0 + t₀ * a 3 - c 0 - t₀ * u 0) +
      V 1 1 * (a 1 + t₀ * a 4 - c 1 - t₀ * u 1),
    a 2 + t₀ * a 5,
    q * (V 0 0 * (a 3 - u 0) + V 0 1 * (a 4 - u 1)),
    q * (V 1 0 * (a 3 - u 0) + V 1 1 * (a 4 - u 1)),
    q * a 5]

noncomputable def normalizedTrajectory (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (l : Trajectory) : Trajectory :=
  (l.1, normalizedCoefficients t₀ q c u V l.2)

theorem normalizedTrajectory_planar (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (l : Trajectory) (τ : ℝ) :
    y (normalizedTrajectory t₀ q c u V l) τ =
      Matrix.toEuclideanLin V (y l (t₀ + q * τ) - c - (t₀ + q * τ) • u) := by
  ext i
  fin_cases i <;>
    simp [y, x, normalizedTrajectory, normalizedCoefficients, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> ring

theorem normalizedTrajectory_hidden (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (l : Trajectory) (τ : ℝ) :
    x (normalizedTrajectory t₀ q c u V l) τ 3 = x l (t₀ + q * τ) 3 := by
  simp [x, normalizedTrajectory, normalizedCoefficients]
  ring

/-- Two native trajectories are determined by their index and two positions. -/
theorem trajectory_ext_of_two_times {a b : Trajectory} (hi : a.1 = b.1)
    (hy₀ : y a 0 = y b 0) (hy₁ : y a 1 = y b 1)
    (hw₀ : x a 0 3 = x b 0 3) (hw₁ : x a 1 3 = x b 1 3) : a = b := by
  have hy00 := congrArg (fun z : Spatial => z 0) hy₀
  have hy01 := congrArg (fun z : Spatial => z 1) hy₀
  have hy10 := congrArg (fun z : Spatial => z 0) hy₁
  have hy11 := congrArg (fun z : Spatial => z 1) hy₁
  simp [y, x] at hy00 hy01 hy10 hy11 hw₀ hw₁
  apply Prod.ext hi
  funext i
  fin_cases i <;> dsimp <;> linarith

/-- The coordinate identities determine the coefficient map itself. This lets
finite-format pullbacks use explicit affine polynomials, even when a remainder
was constructed using an independently bundled measurable equivalence. -/
theorem coefficient_map_eq_normalized {θ : Trajectory → Trajectory}
    (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (hi : ∀ l, (θ l).1 = l.1)
    (hy : ∀ l τ, y (θ l) τ = Matrix.toEuclideanLin V
      (y l (t₀ + q * τ) - c - (t₀ + q * τ) • u))
    (hw : ∀ l τ, x (θ l) τ 3 = x l (t₀ + q * τ) 3) :
    θ = normalizedTrajectory t₀ q c u V := by
  funext l
  apply trajectory_ext_of_two_times (b := normalizedTrajectory t₀ q c u V l) (hi l)
  · rw [hy, normalizedTrajectory_planar]
  · rw [hy, normalizedTrajectory_planar]
  · rw [hw, normalizedTrajectory_hidden]
  · rw [hw, normalizedTrajectory_hidden]

/-- The same six affine formulas, now as polynomials for sign-table pullback. -/
noncomputable def normalizedCoefficientPolynomials (t₀ q : ℝ) (c u : Spatial) (V : Frame) :
    Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![C (V 0 0) * (X 0 + C t₀ * X 3 - C (c 0) - C (t₀ * u 0)) +
      C (V 0 1) * (X 1 + C t₀ * X 4 - C (c 1) - C (t₀ * u 1)),
    C (V 1 0) * (X 0 + C t₀ * X 3 - C (c 0) - C (t₀ * u 0)) +
      C (V 1 1) * (X 1 + C t₀ * X 4 - C (c 1) - C (t₀ * u 1)),
    X 2 + C t₀ * X 5,
    C q * (C (V 0 0) * (X 3 - C (u 0)) + C (V 0 1) * (X 4 - C (u 1))),
    C q * (C (V 1 0) * (X 3 - C (u 0)) + C (V 1 1) * (X 4 - C (u 1))),
    C q * X 5]

theorem eval_normalizedCoefficientPolynomials (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (a : Fin 6 → ℝ) :
    (fun i => eval a (normalizedCoefficientPolynomials t₀ q c u V i)) =
      normalizedCoefficients t₀ q c u V a := by
  funext i
  fin_cases i <;> simp [normalizedCoefficientPolynomials, normalizedCoefficients]

private theorem affine_degree_C_mul {n : ℕ} (r : ℝ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ 1) : (C r * P).totalDegree ≤ 1 :=
  (totalDegree_mul _ _).trans (by simpa using hP)

private theorem affine_degree_add {n : ℕ} {P Q : MvPolynomial (Fin n) ℝ}
    (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1) :
    (P + Q).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hP hQ)

private theorem affine_degree_sub {n : ℕ} {P Q : MvPolynomial (Fin n) ℝ}
    (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1) :
    (P - Q).totalDegree ≤ 1 := (totalDegree_sub _ _).trans (max_le hP hQ)

theorem normalizedCoefficientPolynomials_degree (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (i : Fin 6) : (normalizedCoefficientPolynomials t₀ q c u V i).totalDegree ≤ 1 := by
  have hd (j k : Fin 6) (z v : ℝ) :
      (X j + C t₀ * X k - C z - C (t₀ * v) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    affine_degree_sub (affine_degree_sub
      (affine_degree_add (by simp only [totalDegree_C, totalDegree_X]; omega) (affine_degree_C_mul _ _ (by simp only [totalDegree_C, totalDegree_X]; omega))) (by simp only [totalDegree_C, totalDegree_X]; omega)) (by simp only [totalDegree_C, totalDegree_X]; omega)
  have hs (j : Fin 6) (z : ℝ) : (X j - C z : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    affine_degree_sub (by simp only [totalDegree_C, totalDegree_X]; omega) (by simp only [totalDegree_C, totalDegree_X]; omega)
  fin_cases i <;> dsimp only [normalizedCoefficientPolynomials]
  · exact affine_degree_add (affine_degree_C_mul _ _ (hd _ _ _ _))
      (affine_degree_C_mul _ _ (hd _ _ _ _))
  · exact affine_degree_add (affine_degree_C_mul _ _ (hd _ _ _ _))
      (affine_degree_C_mul _ _ (hd _ _ _ _))
  · exact affine_degree_add (by simp only [totalDegree_C, totalDegree_X]; omega) (affine_degree_C_mul _ _ (by simp only [totalDegree_C, totalDegree_X]; omega))
  · exact affine_degree_C_mul _ _ (affine_degree_add
      (affine_degree_C_mul _ _ (hs _ _)) (affine_degree_C_mul _ _ (hs _ _)))
  · exact affine_degree_C_mul _ _ (affine_degree_add
      (affine_degree_C_mul _ _ (hs _ _)) (affine_degree_C_mul _ _ (hs _ _)))
  · exact affine_degree_C_mul _ _ (by simp only [totalDegree_C, totalDegree_X]; omega)

theorem normalizedTrajectory_format {H : ℝ} {D : ℕ} {A : Set Trajectory}
    (hA : ∀ i, fmt 6 H D {a | (i, a) ∈ A})
    (t₀ q : ℝ) (c u : Spatial) (V : Frame) (i : ℕ) :
    fmt 6 H D {a | normalizedTrajectory t₀ q c u V (i, a) ∈ A} := by
  have ha : Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D {a | (i, a) ∈ A} := hA i
  have ht := ha.affine_preimage (normalizedCoefficientPolynomials t₀ q c u V)
    (normalizedCoefficientPolynomials_degree t₀ q c u V)
  change Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D _
  simpa only [eval_normalizedCoefficientPolynomials, Set.preimage_ofPred_eq, normalizedTrajectory] using ht


/-- Seven affine sign-test coordinates for pulling an entire incidence set
back from a normalized block to the physical coordinates. -/
noncomputable def normalizedIncidencePolynomials (t₀ q : ℝ) (c u : Spatial) (V : Frame) :
    Fin 7 → MvPolynomial (Fin 7) ℝ :=
  Fin.snoc (fun i : Fin 6 => rename Fin.castSucc
    (normalizedCoefficientPolynomials t₀ q c u V i)) (C q⁻¹ * (X 6 - C t₀))

theorem normalizedIncidencePolynomials_degree (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (i : Fin 7) : (normalizedIncidencePolynomials t₀ q c u V i).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [normalizedIncidencePolynomials, Fin.snoc_last]
    exact affine_degree_C_mul _ _ (affine_degree_sub (by simp) (by simp))
  · simp only [normalizedIncidencePolynomials, Fin.snoc_castSucc]
    exact (totalDegree_rename_le _ _).trans (normalizedCoefficientPolynomials_degree _ _ _ _ _ j)

theorem eval_normalizedIncidencePolynomials (t₀ q : ℝ) (c u : Spatial) (V : Frame)
    (a : Fin 7 → ℝ) :
    (fun i => eval a (normalizedIncidencePolynomials t₀ q c u V i)) =
      Fin.snoc (normalizedCoefficients t₀ q c u V (fun j => a j.castSucc)) ((a 6 - t₀) / q) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change eval a (C q⁻¹ * (X 6 - C t₀)) = (a 6 - t₀) / q
    simp [div_eq_mul_inv, mul_comm]
  · simp only [normalizedIncidencePolynomials, Fin.snoc_castSucc, eval_rename]
    exact congrFun (eval_normalizedCoefficientPolynomials t₀ q c u V (fun j => a j.castSucc)) j

theorem normalizedIncidence_format {H : ℝ} {D : ℕ} {F : Set Incidence}
    (hF : ∀ i, fmt 7 H D {a | ((i, fun j : Fin 6 => a j.castSucc), a 6) ∈ F})
    (t₀ q : ℝ) (c u : Spatial) (V : Frame) (i : ℕ) :
    fmt 7 H D {a : Fin 7 → ℝ |
      (normalizedTrajectory t₀ q c u V (i, fun j => a j.castSucc), (a 6 - t₀) / q) ∈ F} := by
  have hf : Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D
      {a : Fin 7 → ℝ | ((i, fun j : Fin 6 => a j.castSucc), a 6) ∈ F} := hF i
  have ht := hf.affine_preimage (normalizedIncidencePolynomials t₀ q c u V)
    (normalizedIncidencePolynomials_degree t₀ q c u V)
  have hcoef (a : Fin 7 → ℝ) :
      (fun j : Fin 6 => eval a (normalizedIncidencePolynomials t₀ q c u V j.castSucc)) =
        normalizedCoefficients t₀ q c u V (fun j => a j.castSucc) := by
    funext j
    simpa only [Fin.snoc_castSucc] using
      congrFun (eval_normalizedIncidencePolynomials t₀ q c u V a) j.castSucc
  have htime (a : Fin 7 → ℝ) :
      eval a (normalizedIncidencePolynomials t₀ q c u V 6) = (a 6 - t₀) / q := by
    change eval a (C q⁻¹ * (X 6 - C t₀)) = (a 6 - t₀) / q
    simp [div_eq_mul_inv, mul_comm]
  change Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D _
  simpa only [Set.preimage_ofPred_eq, hcoef, htime, normalizedTrajectory] using ht

end Submission.Obl.k4_native_finite_terminal_atlas_lift
