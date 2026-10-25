/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

variable {R : Type*} [CommSemiring R]

/-- The standard binary polynomial encoding, with variable zero outermost. -/
noncomputable def binaryPolynomialEncoding (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R) :=
  (Polynomial.mapRingHom (uniqueAlgEquiv R (Fin 1)).toRingHom).comp (finSuccEquiv R 1).toRingHom

/-- The standard ternary polynomial encoding, with variable zero outermost. -/
noncomputable def ternaryPolynomialEncoding (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 3) R →+* Polynomial (Polynomial (Polynomial R)) :=
  (Polynomial.mapRingHom (binaryPolynomialEncoding R)).comp (finSuccEquiv R 2).toRingHom

theorem finSuccEquiv_coeff_totalDegree_le {n : ℕ} (F : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    ((finSuccEquiv R n F).coeff i).totalDegree ≤ F.totalDegree := by
  by_cases hz : (finSuccEquiv R n F).coeff i = 0
  · simp [hz]
  · have h := totalDegree_coeff_finSuccEquiv_add_le F i hz
    omega

theorem uniqueAlgEquiv_natDegree_le (F : MvPolynomial (Fin 1) R) :
    (uniqueAlgEquiv R (Fin 1) F).natDegree ≤ F.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_uniqueAlgEquiv]
  apply coeff_eq_zero_of_totalDegree_lt
  change F.totalDegree < (Finsupp.single (default : Fin 1) n).degree
  rw [Finsupp.degree_single]
  exact hn

theorem binaryPolynomialEncoding_natDegree_le (F : MvPolynomial (Fin 2) R) :
    (binaryPolynomialEncoding R F).natDegree ≤ F.totalDegree := by
  change (Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom (finSuccEquiv R 1 F)).natDegree ≤ _
  exact Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv F).trans_le (degreeOf_le_totalDegree F 0))

theorem binaryPolynomialEncoding_coeff_natDegree_le (F : MvPolynomial (Fin 2) R) (i : ℕ) :
    ((binaryPolynomialEncoding R F).coeff i).natDegree ≤ F.totalDegree := by
  change (Polynomial.coeff (Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom (finSuccEquiv R 1 F)) i).natDegree ≤ _
  rw [Polynomial.coeff_map]
  exact (uniqueAlgEquiv_natDegree_le _).trans (finSuccEquiv_coeff_totalDegree_le F i)

theorem binaryPolynomialEncoding_coeff_coeff (F : MvPolynomial (Fin 2) R) (i j : ℕ) :
    ((binaryPolynomialEncoding R F).coeff i).coeff j = F.coeff ((Finsupp.single (0 : Fin 1) j).cons i) := by
  change (Polynomial.coeff (Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom (finSuccEquiv R 1 F)) i).coeff j = _
  rw [Polynomial.coeff_map]
  change (uniqueAlgEquiv R (Fin 1) ((finSuccEquiv R 1 F).coeff i)).coeff j = _
  rw [coeff_uniqueAlgEquiv, finSuccEquiv_coeff_coeff]
  rfl

theorem eval_binaryPolynomialEncoding (F : MvPolynomial (Fin 2) R) (x y : R) :
    ((binaryPolynomialEncoding R F).map (Polynomial.evalRingHom x)).eval y =
      MvPolynomial.eval ![y, x] F := by
  have heval : (Polynomial.evalRingHom x).comp (uniqueAlgEquiv R (Fin 1)).toRingHom =
      MvPolynomial.eval (fun _ : Fin 1 => x) := by
    apply RingHom.ext
    intro P
    change (uniqueAlgEquiv R (Fin 1) P).eval x = MvPolynomial.eval (fun _ : Fin 1 => x) P
    exact eval₂_const_uniqueAlgEquiv (φ := RingHom.id R) (a := x)
  change (Polynomial.map (Polynomial.evalRingHom x) (Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom (finSuccEquiv R 1 F))).eval y = _
  rw [Polynomial.map_map, heval]
  have hvec : ![y, x] = Fin.cons y (fun _ : Fin 1 => x) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  exact (eval_eq_eval_mv_eval' (fun _ : Fin 1 => x) y F).symm

theorem ternaryPolynomialEncoding_natDegree_le (F : MvPolynomial (Fin 3) R) :
    (ternaryPolynomialEncoding R F).natDegree ≤ F.totalDegree := by
  change (Polynomial.map (binaryPolynomialEncoding R) (finSuccEquiv R 2 F)).natDegree ≤ _
  exact Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv F).trans_le (degreeOf_le_totalDegree F 0))

theorem ternaryPolynomialEncoding_coeff_natDegree_le (F : MvPolynomial (Fin 3) R) (i : ℕ) :
    ((ternaryPolynomialEncoding R F).coeff i).natDegree ≤ F.totalDegree := by
  change (Polynomial.coeff (Polynomial.map (binaryPolynomialEncoding R) (finSuccEquiv R 2 F)) i).natDegree ≤ _
  rw [Polynomial.coeff_map]
  exact (binaryPolynomialEncoding_natDegree_le _).trans (finSuccEquiv_coeff_totalDegree_le F i)

theorem ternaryPolynomialEncoding_coeff_coeff_natDegree_le (F : MvPolynomial (Fin 3) R) (i j : ℕ) :
    (((ternaryPolynomialEncoding R F).coeff i).coeff j).natDegree ≤ F.totalDegree := by
  change ((Polynomial.coeff (Polynomial.map (binaryPolynomialEncoding R) (finSuccEquiv R 2 F)) i).coeff j).natDegree ≤ _
  rw [Polynomial.coeff_map]
  exact (binaryPolynomialEncoding_coeff_natDegree_le _ j).trans (finSuccEquiv_coeff_totalDegree_le F i)

theorem ternaryPolynomialEncoding_coeff_coeff_coeff (F : MvPolynomial (Fin 3) R) (i j k : ℕ) :
    (((ternaryPolynomialEncoding R F).coeff i).coeff j).coeff k =
      F.coeff (((Finsupp.single (0 : Fin 1) k).cons j).cons i) := by
  change ((Polynomial.coeff (Polynomial.map (binaryPolynomialEncoding R) (finSuccEquiv R 2 F)) i).coeff j).coeff k = _
  rw [Polynomial.coeff_map, binaryPolynomialEncoding_coeff_coeff, finSuccEquiv_coeff_coeff]

theorem eval_ternaryPolynomialEncoding (F : MvPolynomial (Fin 3) R) (x y z : R) :
    ((ternaryPolynomialEncoding R F).map ((Polynomial.evalRingHom y).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom x)))).eval z = MvPolynomial.eval ![z, y, x] F := by
  have heval : ((Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))).comp
      (binaryPolynomialEncoding R) = MvPolynomial.eval ![y, x] := by
    apply RingHom.ext
    intro P
    exact eval_binaryPolynomialEncoding P x y
  change (Polynomial.map ((Polynomial.evalRingHom y).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom x)))
    (Polynomial.map (binaryPolynomialEncoding R) (finSuccEquiv R 2 F))).eval z = _
  rw [Polynomial.map_map, heval]
  have hvec : ![z, y, x] = Fin.cons z ![y, x] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  exact (eval_eq_eval_mv_eval' ![y, x] z F).symm

end Submission.Lib.K4PolynomialNorming
