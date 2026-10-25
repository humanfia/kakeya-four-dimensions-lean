/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/QuarticConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/QuarticConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.PolynomialCoefficientBounds
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ParallelConditioning

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

noncomputable def cubicConicError (A κ ε : ℝ) : ℝ := 1512 * A ^ 6 / κ ^ 3 * ε

noncomputable def quarticParallelError (A κ R S T U V ε : ℝ) : ℝ :=
  27 * U * V * S * (5 * R ^ 4 * (9 * (3 * S * T) ^ 2 * (54 * A ^ 2 * cubicConicError A κ ε)))

noncomputable def quarticConicError (A κ Qbound R S T U V ε : ℝ) : ℝ :=
  3 * (cubicConicError A κ ε + 3 * Qbound * quarticParallelError A κ R S T U V ε)

/-- Explicit conditioning of the quartic conic kernel. The frame and gradient
bounds are kept as parameters so callers can insert their own determinant
bounds without another compactness argument. -/
theorem exists_quartic_conic_approximation
    (p : Fin 7 → Fin 3 → ℝ) (A κ Qbound R S T U V ε : ℝ)
    (hA : 0 ≤ A) (hκ : 0 < κ) (hQbound : 0 ≤ Qbound)
    (hR : 1 ≤ R) (hS : 0 ≤ S) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (hqcoeff : ∀ m, |q.coeff m| ≤ Qbound)
    (B P : Matrix (Fin 3) (Fin 3) ℝ) (hBdet : IsUnit B.det) (hPdet : IsUnit P.det)
    (hgrad : ∀ x : Fin 3 → ℝ, ∀ j, MvPolynomial.eval x (pderiv j q) = Matrix.mulVec B x j)
    (α : Fin 3 → ℝ) (hα : ∀ i, |α i| ≤ R) (hlow : ∀ i, 1 ≤ R * |α i|)
    (hPinv : ∀ i j, |P⁻¹ i j| ≤ S) (hBinv : ∀ i j, |B⁻¹ i j| ≤ T)
    (hB : ∀ i j, |B i j| ≤ U) (hP : ∀ i j, |P i j| ≤ V)
    (hframe : ∀ i : Fin 3, p (Fin.castLE (by decide : 3 ≤ 7) i) = fun l => P l i)
    (hextra : p 3 = Matrix.mulVec P α)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hsmall : ∀ i j, |MvPolynomial.eval (p i) (pderiv j F)| ≤ ε) :
    ∃ r : ℝ, ∀ m : Fin 3 →₀ ℕ,
      |(F - C r * q ^ 2).coeff m| ≤ quarticConicError A κ Qbound R S T U V ε := by
  classical
  let D := cubicConicError A κ ε
  have hD : 0 ≤ D := by dsimp [D, cubicConicError]; positivity
  have hFd (j : Fin 3) : (pderiv j F).IsHomogeneous 3 := by simpa using hF.pderiv
  have hexists (j : Fin 3) : ∃ L : MvPolynomial (Fin 3) ℝ, L.IsHomogeneous 1 ∧
      ∀ m, |(pderiv j F - q * L).coeff m| ≤ D :=
    exists_cubic_conic_approximation p A κ ε hA hκ hε hcoord hp q hq hne hqzero
      (pderiv j F) (hFd j) (fun i => hsmall i j)
  choose L hL hEc using hexists
  let E (j : Fin 3) := pderiv j F - q * L j
  have hEhom (j : Fin 3) : (E j).IsHomogeneous 3 := (hFd j).sub (hq.mul (hL j))
  have hEcoeff (j : Fin 3) (m : Fin 3 →₀ ℕ) : |(E j).coeff m| ≤ D := hEc j m
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun j k => (pderiv k (L j)).coeff 0
  have hLpoly (j : Fin 3) : L j = linearPolynomial (fun k => M j k) :=
    homogeneous_one_eq_sum_linear (L j) (hL j)
  have hLeval (j : Fin 3) (x : Fin 3 → ℝ) :
      MvPolynomial.eval x (L j) = Matrix.mulVec M x j := by
    rw [hLpoly j]
    simp [linearPolynomial, Matrix.mulVec, dotProduct]
  have hqpoly (j : Fin 3) : pderiv j q = linearPolynomial (fun k => B j k) := by
    apply MvPolynomial.funext
    intro x
    simpa [linearPolynomial, Matrix.mulVec, dotProduct] using hgrad x j
  have hEdcoeff (j k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv k (E j)).coeff m| ≤ 3 * D :=
    coeff_pderiv_abs_le_of_totalDegree (E j) 3 (hEhom j).totalDegree_le D hD (hEcoeff j) k m
  have hEdvalue (i : Fin 7) (j k : Fin 3) :
      |MvPolynomial.eval (p i) (pderiv k (E j))| ≤ 27 * A ^ 2 * D := by
    convert homogeneous_eval_abs_le A hA (p i) (hcoord i) 2 (pderiv k (E j))
      (by simpa using (hEhom j).pderiv) (3 * D) (by positivity) (hEdcoeff j k) using 1 <;> ring
  have hcrossEq (i : Fin 7) (j k : Fin 3) :
      crossCoordinate (Matrix.mulVec B (p i)) (Matrix.mulVec M (p i)) j k =
        MvPolynomial.eval (p i) (pderiv j (E k)) - MvPolynomial.eval (p i) (pderiv k (E j)) := by
    dsimp [crossCoordinate]
    rw [← hgrad (p i) k, ← hgrad (p i) j, ← hLeval j (p i), ← hLeval k (p i)]
    dsimp [E]
    simp only [map_sub, pderiv_mul, map_sub, map_add, map_mul, hqzero i,
      zero_mul, add_zero]
    rw [polynomial_pderiv_comm F j k]
    ring
  let ζ := 54 * A ^ 2 * D
  have hζ : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hcross (i : Fin 7) (j k : Fin 3) :
      |crossCoordinate (Matrix.mulVec B (p i)) (Matrix.mulVec M (p i)) j k| ≤ ζ := by
    rw [hcrossEq]
    calc
      _ ≤ |MvPolynomial.eval (p i) (pderiv j (E k))| +
          |MvPolynomial.eval (p i) (pderiv k (E j))| := abs_sub _ _
      _ ≤ 27 * A ^ 2 * D + 27 * A ^ 2 * D := add_le_add (hEdvalue i k j) (hEdvalue i j k)
      _ = _ := by dsimp [ζ]; ring
  obtain ⟨r, hr⟩ := matrix_near_proportional_of_frame_cross_tests M B P hBdet hPdet α R S T U V ζ
    hR hS hT hU hV hζ hα hlow hPinv hBinv hB hP
    (fun i j k => by simpa only [hframe i] using hcross (Fin.castLE (by decide : 3 ≤ 7) i) j k)
    (fun j k => by simpa only [hextra] using hcross 3 j k)
  let η := quarticParallelError A κ R S T U V ε
  have hη : 0 ≤ η := by dsimp [η, quarticParallelError, cubicConicError]; positivity
  have hrcoeff (j k : Fin 3) : |M j k - r * B j k| ≤ η := by
    simpa only [η, quarticParallelError, ζ, D, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hr j k
  have hDpoly (j : Fin 3) :
      L j - C r * pderiv j q = linearPolynomial (fun k => M j k - r * B j k) := by
    rw [hLpoly j, hqpoly j]
    simp only [linearPolynomial, Finset.mul_sum, ← Finset.sum_sub_distrib, map_sub, map_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  let H := F - C (r / 2) * q ^ 2
  have hHhom : H.IsHomogeneous 4 := by
    dsimp [H]
    rw [pow_two]
    exact hF.sub ((hq.mul hq).C_mul (r / 2))
  have hscalar : C (r / 2) * (2 : MvPolynomial (Fin 3) ℝ) = C r := by
    calc
      _ = C (r / 2) * C (2 : ℝ) := by rw [map_ofNat]
      _ = C ((r / 2) * 2) := (map_mul C _ _).symm
      _ = _ := by congr 1; ring
  have hderH (j : Fin 3) : pderiv j H = E j + q * (L j - C r * pderiv j q) := by
    dsimp [H, E]
    rw [map_sub, pderiv_C_mul, pow_two, pderiv_mul]
    calc
      pderiv j F - C (r / 2) * (pderiv j q * q + q * pderiv j q) =
          pderiv j F - (C (r / 2) * 2) * q * pderiv j q := by ring
      _ = _ := by rw [hscalar]; ring
  have hderHcoeff (j : Fin 3) (m : Fin 3 →₀ ℕ) :
      |(pderiv j H).coeff m| ≤ D + 3 * Qbound * η := by
    rw [hderH j, MvPolynomial.coeff_add]
    apply (abs_add_le _ _).trans
    apply add_le_add (hEcoeff j m)
    rw [hDpoly j]
    exact coeff_mul_linearPolynomial_abs_le q _ Qbound η hQbound hη hqcoeff (hrcoeff j) m
  refine ⟨r / 2, ?_⟩
  intro m
  change |H.coeff m| ≤ 3 * (D + 3 * Qbound * η)
  exact homogeneous_coeff_abs_le_of_pderiv H 4 (by decide) hHhom _ (by positivity) hderHcoeff m

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
