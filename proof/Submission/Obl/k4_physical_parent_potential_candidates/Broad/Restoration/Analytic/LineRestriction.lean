-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/LineRestriction.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/LineRestriction.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/LineRestriction.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RationalSquareRoot
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.PolyAlgebra
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- Restrict a base polynomial to `a + t*v`, keeping one base variable. -/
def complexLineRestriction {n : ℕ} (a v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin 1) ℂ :=
  bind₁ (fun i => C (a i) + C (v i) * X 0) P

theorem complexLineRestriction_totalDegree {n : ℕ} (a v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    (complexLineRestriction a v P).totalDegree ≤ P.totalDegree := by
  apply k4_remainder_pure_profile_normalization.Normalization.totalDegree_bind₁_le_of_le_one
  intro i
  apply (totalDegree_add _ _).trans
  exact max_le (by simp) ((totalDegree_mul _ _).trans (by simp))

theorem eval_complexLineRestriction {n : ℕ} (a v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (t : ℂ) :
    eval (fun _ : Fin 1 => t) (complexLineRestriction a v P) =
      eval (fun i => a i + t * v i) P := by
  change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin n → ℂ => eval₂Hom (RingHom.id ℂ) f P)
  funext i
  simp [mul_comm]

/-- A nonzero denominator value at one anchor prevents the restricted
denominator polynomial from vanishing identically. -/
theorem complexLineRestriction_ne_zero {n : ℕ} (a v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (hP : eval a P ≠ 0) :
    complexLineRestriction a v P ≠ 0 := by
  intro hzero
  have heq := eval_complexLineRestriction a v P 0
  rw [hzero, map_zero] at heq
  exact hP (by simpa using heq.symm)

/-- A branch error relative to any affine hidden trajectory has a uniform
nonzero one-dimensional relation. A single nonzero denominator value is
explicit: a globally nonzero polynomial can vanish on a whole line. -/
theorem exists_affine_line_error_relation {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (a v : Fin n → ℂ) (α β : ℂ) (hWa : eval a W ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P ≠ 0 ∧ P.totalDegree ≤ 8 * (D + 1) + 2 ∧
      ∀ t s g : ℂ, s ^ 2 = eval (fun i => a i + t * v i) Δ →
        eval (fun i => a i + t * v i) W * g =
          eval (fun i => a i + t * v i) U +
            eval (fun i => a i + t * v i) V * s →
        eval (Fin.snoc (fun _ : Fin 1 => t) (g - α - β * t)) P = 0 := by
  let Δ' := complexLineRestriction a v Δ
  let V' := complexLineRestriction a v V
  let W' := complexLineRestriction a v W
  let A : MvPolynomial (Fin 1) ℂ := C α + C β * X 0
  let U' := complexLineRestriction a v U - W' * A
  have hΔ' : Δ'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v Δ).trans hΔ
  have hV' : V'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v V).trans hV
  have hW' : W'.totalDegree ≤ D := (complexLineRestriction_totalDegree a v W).trans hW
  have hA : A.totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    exact max_le (by simp) ((totalDegree_mul _ _).trans (by simp))
  have hU' : U'.totalDegree ≤ D + 1 :=
    (totalDegree_sub _ _).trans (max_le
      (((complexLineRestriction_totalDegree a v U).trans hU).trans (by omega))
      ((totalDegree_mul _ _).trans (add_le_add hW' hA)))
  refine ⟨sqrtRationalRelation Δ' U' V' W',
    sqrtRationalRelation_ne_zero Δ' U' V' W' (complexLineRestriction_ne_zero a v W hWa),
    (sqrtRationalRelation_totalDegree Δ' U' V' W').trans (by omega), ?_⟩
  intro t s g hs hg
  apply eval_sqrtRationalRelation Δ' U' V' W' (fun _ : Fin 1 => t) s (g - α - β * t)
  · simpa only [Δ', eval_complexLineRestriction] using hs
  · dsimp [U', V', W', A]
    simp only [map_sub, map_mul, map_add, eval_C, eval_X, eval_complexLineRestriction]
    linear_combination hg

/-- The exact one-dimensional sheet-relation interface used by the
directional dense-set estimates. The affine line need only map the
standard complex ball into the domain of the branch identities. -/
theorem hasSheetRelation_affine_line_error {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (Ω : Set (EuclideanSpace ℂ (Fin n)))
    (s F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ Ω, eval (fun i => z i) W * F z =
      eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (a v : EuclideanSpace ℂ (Fin n)) (α β : ℂ)
    (hWa : eval (fun i => a i) W ≠ 0)
    (hmap : Set.MapsTo (fun z : EuclideanSpace ℂ (Fin 1) => a + z 0 • v)
      (Metric.ball 0 4) Ω) :
    k4_algebraic_real_jet_comparison.HasSheetRelation 1 (8 * (D + 1) + 2)
      (fun z => F (a + z 0 • v) - α - β * z 0) := by
  obtain ⟨P, hPne, hPdeg, hPrel⟩ := exists_affine_line_error_relation D Δ U V W
    hΔ hU hV hW (fun i => a i) (fun i => v i) α β hWa
  refine ⟨P, hPne, hPdeg, ?_⟩
  intro z hz
  have hrootLine : (s (a + z 0 • v)) ^ 2 =
      eval (fun i => a i + z 0 * v i) Δ := by
    simpa using hroot (a + z 0 • v) (hmap hz)
  have hrepLine : eval (fun i => a i + z 0 * v i) W * F (a + z 0 • v) =
      eval (fun i => a i + z 0 * v i) U +
        eval (fun i => a i + z 0 * v i) V * s (a + z 0 • v) := by
    simpa using hrep (a + z 0 • v) (hmap hz)
  have heq := hPrel (z 0) (s (a + z 0 • v)) (F (a + z 0 • v)) hrootLine hrepLine
  have hcoord : (fun _ : Fin 1 => z 0) = (fun i => z i) := by
    funext i
    fin_cases i
    rfl
  simpa only [hcoord] using heq

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
