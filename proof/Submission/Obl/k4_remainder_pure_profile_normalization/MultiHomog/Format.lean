import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Encode
import Submission.Obl.k4_eligibility_sign_description.Families

/-!
# The frozen sign format under affine changes of coordinates

`fmt n H D S` (at most `H` sign tests of degree at most `D`, combined by a Boolean
function) is preserved by preimages under polynomial maps of degree at most one. In
particular trajectory pieces and incidence slices keep their format under the diagonal
affine coefficient changes `encCoeff` and `decCoeff` of the world encoding.
The diagonal affine maps follow the design of this tree's o147/x0502
`Homogenize/AffineFormat.lean`; the proofs here are written for `fmt`.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MvPolynomial

theorem fmt_mono {n : ℕ} {H H' : ℝ} {D D' : ℕ} {S : Set (Fin n → ℝ)} (h : fmt n H D S)
    (hH : H ≤ H') (hD : D ≤ D') : fmt n H' D' S := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  exact ⟨m, hm.trans hH, p, fun i => (hp i).trans hD, b, hb⟩

theorem fmt_empty {n : ℕ} {H : ℝ} (hH : 0 ≤ H) (D : ℕ) : fmt n H D (∅ : Set (Fin n → ℝ)) :=
  ⟨0, by simpa using hH, Fin.elim0, fun i => i.elim0, fun _ => false, fun x => by simp⟩

theorem fmt_congr {n : ℕ} {H : ℝ} {D : ℕ} {S T : Set (Fin n → ℝ)} (h : fmt n H D S)
    (hST : S = T) : fmt n H D T := hST ▸ h

/-- Preimage under a polynomial map of degree at most one. -/
theorem fmt_preimage {n k : ℕ} {H : ℝ} {D : ℕ} {S : Set (Fin n → ℝ)} (h : fmt n H D S)
    (σ : Fin n → MvPolynomial (Fin k) ℝ) (hσ : ∀ i, (σ i).totalDegree ≤ 1) :
    fmt k H D {x : Fin k → ℝ | (fun i => eval x (σ i)) ∈ S} := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, fun i => aeval σ (p i), fun i =>
    (k4_eligibility_sign_description.degree_aeval_le (p i) σ hσ).trans (hp i), b, fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, k4_eligibility_sign_description.eval_aeval_real]
  exact hb _

/-- A diagonal affine map of coefficients. -/
def diagAffine (d c : Fin 6 → ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ := fun j => d j * x j + c j

theorem encCoeff_eq_diagAffine (a b θ o : ℝ) :
    encCoeff a b θ o = diagAffine (encDiag a b θ) (encShift o) := by
  funext x j
  fin_cases j <;> simp [encCoeff, diagAffine, encDiag, encShift]

theorem decCoeff_eq_diagAffine (a b θ o : ℝ) :
    decCoeff a b θ o =
      diagAffine (fun j => (encDiag a b θ j)⁻¹) (fun j => -(encShift o j / encDiag a b θ j)) := by
  funext x j
  fin_cases j <;> simp [decCoeff, diagAffine, encDiag, encShift] <;> ring

theorem totalDegree_affine_le {k : ℕ} (d c : ℝ) (j : Fin k) :
    (C d * X j + C c : MvPolynomial (Fin k) ℝ).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by simp)) (by simp))

/-- Formats of trajectory pieces are preserved by diagonal affine preimages. -/
theorem fmt_diagAffine {H : ℝ} {D : ℕ} {A : Set (Fin 6 → ℝ)} (h : fmt 6 H D A)
    (d c : Fin 6 → ℝ) : fmt 6 H D {x | diagAffine d c x ∈ A} := by
  have := fmt_preimage h (fun j => C (d j) * X j + C (c j)) (fun j => totalDegree_affine_le _ _ j)
  refine fmt_congr this ?_
  ext z
  simp only [Set.mem_ofPred_eq, map_add, map_mul, eval_C, eval_X]
  rfl

/-- The coordinate change acting on the coefficient part of a point of `ℝ⁷`. -/
noncomputable def sliceAffine (d c : Fin 6 → ℝ) : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  fun m => if h : (m : ℕ) < 6 then C (d ⟨m, h⟩) * X m + C (c ⟨m, h⟩) else X m

theorem sliceAffine_degree (d c : Fin 6 → ℝ) (m : Fin 7) :
    (sliceAffine d c m).totalDegree ≤ 1 := by
  unfold sliceAffine
  split_ifs
  · exact totalDegree_affine_le _ _ _
  · simp

theorem eval_sliceAffine_castSucc (d c : Fin 6 → ℝ) (x : Fin 7 → ℝ) (j : Fin 6) :
    eval x (sliceAffine d c j.castSucc) = d j * x j.castSucc + c j := by
  have hj : ((j.castSucc : Fin 7) : ℕ) < 6 := by simp
  simp only [sliceAffine, hj, dite_true]
  simp

theorem eval_sliceAffine_six (d c : Fin 6 → ℝ) (x : Fin 7 → ℝ) :
    eval x (sliceAffine d c 6) = x 6 := by
  simp [sliceAffine]

/-- Formats of incidence slices are preserved by diagonal affine changes of the
coefficients, at any fixed pair of indices. -/
theorem fmt_slice_diagAffine {H : ℝ} {D : ℕ} {E : Set Incidence} {i : ℕ}
    (h : fmt 7 H D {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E})
    (d c : Fin 6 → ℝ) :
    fmt 7 H D {x : Fin 7 → ℝ |
      ((i, diagAffine d c (fun j : Fin 6 => x j.castSucc)), x 6) ∈ E} := by
  have := fmt_preimage h (sliceAffine d c) (sliceAffine_degree d c)
  refine fmt_congr this ?_
  ext z
  have e1 : diagAffine d c (fun j : Fin 6 => z j.castSucc) =
      fun j : Fin 6 => eval z (sliceAffine d c j.castSucc) := by
    funext j
    rw [eval_sliceAffine_castSucc]
    rfl
  have e2 : eval z (sliceAffine d c 6) = z 6 := eval_sliceAffine_six d c z
  simp only [Set.mem_ofPred_eq]
  rw [e1, e2]

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
