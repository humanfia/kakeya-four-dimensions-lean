/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftGeometry.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftAtlas
import Submission.Obl.k4_native_finite_terminal_atlas_lift.ScaleTransport

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

theorem initialTime_bounds (k : ℕ) (b : Fin (q.W k)) :
    0 ≤ rem.initialTime k b ∧ rem.initialTime k b ≤ 1 := by
  have hj : (((rem.parent k).j (rem.parentIndex k b) : ℕ) : ℝ) <
      (2 : ℝ) ^ (rem.parent k).T := by exact_mod_cast ((rem.parent k).j (rem.parentIndex k b)).isLt
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · exact le_of_lt ((div_lt_one (by positivity)).mpr hj)

theorem time_roundtrip (k : ℕ) (b : Fin (q.W k)) (t : ℝ) :
    rem.initialTime k b + rem.timeLength k * ((t - rem.initialTime k b) / rem.timeLength k) = t :=
  (timeEquiv (rem.initialTime k b) (rem.timeLength k) (rem.timeLength_pos k).ne').apply_symm_apply t

theorem liftAtlas_time {k : ℕ} (a : Atlas q k) (b : Fin a.C) {t : ℝ}
    (ht : t ∈ Set.Icc (((rem.liftAtlas k a).j b : ℝ) / (2 : ℝ) ^ (rem.liftAtlas k a).T)
      ((((rem.liftAtlas k a).j b : ℝ) + 1) / (2 : ℝ) ^ (rem.liftAtlas k a).T)) :
    (t - rem.initialTime k (a.γ b)) / rem.timeLength k ∈
      Set.Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T) (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T) := by
  have heq : rem.initialTime k (a.γ b) +
      ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) /
        (2 : ℝ) ^ (rem.parent k).T = t := by
    simpa only [timeLength, div_eq_mul_inv, mul_comm] using rem.time_roundtrip k (a.γ b) t
  apply (compositeBlock_interval ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b) _).mp
  change rem.initialTime k (a.γ b) +
    ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) / (2 : ℝ) ^ (rem.parent k).T ∈ _
  rw [heq]
  exact ht

theorem liftAtlas_spatial_residual {k M D : ℕ} {a : Atlas q k} (ha : a.TrueAt M D q.L)
    (b : Fin a.C) (l : Trajectory) (t : ℝ) :
    Matrix.toEuclideanLin ((rem.liftAtlas k a).Q b)⁻¹
      (y l t - (rem.liftAtlas k a).c b - t • (rem.liftAtlas k a).u b) =
    Matrix.toEuclideanLin (a.Q b)⁻¹
      (y (rem.coefficient_map k (a.γ b) l) ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) -
        a.c b - ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) • a.u b) := by
  have hQ := ((rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))).1
  change Matrix.toEuclideanLin ((rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b)⁻¹
    (y l t - compositeCenter (rem.initialTime k (a.γ b)) (rem.timeLength k)
      ((rem.parent k).c (rem.parentIndex k (a.γ b))) (a.c b)
      ((rem.parent k).u (rem.parentIndex k (a.γ b))) (a.u b)
      ((rem.parent k).Q (rem.parentIndex k (a.γ b))) -
      t • compositeVelocity (rem.timeLength k) ((rem.parent k).u (rem.parentIndex k (a.γ b)))
        (a.u b) ((rem.parent k).Q (rem.parentIndex k (a.γ b)))) = _
  rw [composite_frame_residual _ _ _ (rem.timeLength_pos k).ne' _ _ _ _ _ _ _ hQ]
  have hy := rem.planar_map k (a.γ b) l ((t - rem.initialTime k (a.γ b)) / rem.timeLength k)
  have heq := rem.time_roundtrip k (a.γ b) t
  have heq' : rem.initialTime k (a.γ b) +
      ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) /
        (2 : ℝ) ^ (rem.parent k).T = t := by
    simpa only [timeLength, div_eq_mul_inv, mul_comm] using heq
  change y _ _ = Matrix.toEuclideanLin _ (y l
    (rem.initialTime k (a.γ b) + _ / (2 : ℝ) ^ (rem.parent k).T) - _ -
      (rem.initialTime k (a.γ b) + _ / (2 : ℝ) ^ (rem.parent k).T) • _) at hy
  rw [heq'] at hy
  rw [hy]

/-- Native test evaluation through the actual retained coefficient map. -/
theorem native_lifted_test_evaluation (k : ℕ) (b : Fin (q.W k)) (P : Test)
    (l : Trajectory) (t : ℝ) :
    MvPolynomial.eval (x l t)
      (liftedTest (δ (p.N (rem.φ k)) r) (rem.initialTime k b) (rem.timeLength k)
        ((rem.parent k).c (rem.parentIndex k b)) ((rem.parent k).u (rem.parentIndex k b))
        ((rem.parent k).Q (rem.parentIndex k b))⁻¹ P) =
      δ (p.N (rem.φ k)) r * MvPolynomial.eval
        (x (rem.coefficient_map k b l) ((t - rem.initialTime k b) / rem.timeLength k)) P := by
  have ht := eval_liftedTest (δ (p.N (rem.φ k)) r) (rem.initialTime k b)
    (rem.timeLength k) (rem.timeLength_pos k).ne'
    ((rem.parent k).c (rem.parentIndex k b)) ((rem.parent k).u (rem.parentIndex k b))
    ((rem.parent k).Q (rem.parentIndex k b))⁻¹ P l
    ((t - rem.initialTime k b) / rem.timeLength k)
  rw [rem.time_roundtrip k b t] at ht
  rw [rem.coefficient_map_formula k b]
  exact ht

/-- The lifted native test is exactly the child's test multiplied by the
parent depth thickness, at every physical trajectory and time. -/
theorem liftAtlas_test_evaluation {k : ℕ} (a : Atlas q k) (b : Fin a.C)
    (l : Trajectory) (t : ℝ) :
    MvPolynomial.eval (x l t) ((rem.liftAtlas k a).R b) =
      δ (p.N (rem.φ k)) r * MvPolynomial.eval
        (x (rem.coefficient_map k (a.γ b) l)
          ((t - rem.initialTime k (a.γ b)) / rem.timeLength k)) (a.R b) :=
  rem.native_lifted_test_evaluation k (a.γ b) (a.R b) l t

theorem liftAtlas_test_pderiv_evaluation {k : ℕ} (a : Atlas q k) (b : Fin a.C)
    (l : Trajectory) (t : ℝ) :
    MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) ((rem.liftAtlas k a).R b)) =
      δ (p.N (rem.φ k)) r * MvPolynomial.eval
        (x (rem.coefficient_map k (a.γ b) l)
          ((t - rem.initialTime k (a.γ b)) / rem.timeLength k))
        (MvPolynomial.pderiv (3 : Fin 4) (a.R b)) := by
  change MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (liftedTest _ _ _ _ _ _ _)) = _
  rw [liftedTest_pderiv]
  exact rem.native_lifted_test_evaluation k (a.γ b) _ l t

theorem liftAtlas_test_pderiv_pderiv_evaluation {k : ℕ} (a : Atlas q k) (b : Fin a.C)
    (l : Trajectory) (t : ℝ) :
    MvPolynomial.eval (x l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) ((rem.liftAtlas k a).R b))) =
      δ (p.N (rem.φ k)) r * MvPolynomial.eval
        (x (rem.coefficient_map k (a.γ b) l)
          ((t - rem.initialTime k (a.γ b)) / rem.timeLength k))
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (a.R b))) := by
  change MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
    (MvPolynomial.pderiv (3 : Fin 4) (liftedTest _ _ _ _ _ _ _))) = _
  rw [liftedTest_pderiv_pderiv]
  exact rem.native_lifted_test_evaluation k (a.γ b) _ l t

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
