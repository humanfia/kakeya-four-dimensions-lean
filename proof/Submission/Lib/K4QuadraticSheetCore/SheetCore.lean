import Mathlib
import Submission.Lib.K4PolynomialRemezThree.Comparison
import Submission.Lib.K4HorizontalCoercivity.HorizontalInterpolation
import Submission.Lib.K4QuadraticSheetCore.PolyBounds
import Submission.Lib.K4QuadraticSheetCore.SheetFrame

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# The deterministic affine-sheet core: bounding the projected second fundamental form

Normalized setting: base points in the unit cube `[0,1]³`, full-time lines `b` whose base
points stay in the cube, on which the quadratic test `γ + β w + α w²` and its hidden
derivative are bounded by `Λ`. If on a base set `E` of volume at least `Λ⁻¹` every point has
three lines passing within `ℓ¹` distance `ρ`, with pairwise `Λ⁻¹`-separated velocities and
an event (`|G_w| ≥ Λ⁻¹`) on the first one, and the curvature is low (`8|α|Λ³ ≤ 1`), then all
six frame components of the projected second fundamental form are bounded on the whole cube
by `400 Λ³ κ`, provided the contact error `ε` and the mesh `ρ` are small compared to `κ`.

The proof: line bound and frame decomposition at the witnesses; interpolation of the
horizontal components at three velocities; Remez on `E` and coefficient bounds for their
derivatives; the Heisenberg recovery identities on `E`, where the discriminant is at least
`Λ⁻²/4`; Remez again. The contact and mesh errors are absorbed in the coefficient norm of
the six components (they are polynomials), so no a priori bound on the test is needed.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4ChartLifting

noncomputable section

/-- `ℓ¹` distance of base points. -/
def l1dist (x y : Fin 3 → ℝ) : ℝ := |x 0 - y 0| + |x 1 - y 1| + |x 2 - y 2|

theorem abs_le_one_of_mem_cube {p : Fin 3 → ℝ} (hp : p ∈ Icc (0 : Fin 3 → ℝ) 1) (i : Fin 3) :
    |p i| ≤ 1 := by
  have h0 : (0 : ℝ) ≤ p i := hp.1 i
  have h1 : p i ≤ 1 := hp.2 i
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem abs_eval_pderiv_le_cube (P : BasePoly) (p : Fin 3 → ℝ) (hp : ∀ i, |p i| ≤ 1)
    (k : Fin 3) : |eval p (pderiv k P)| ≤ P.totalDegree * coeffL1 P :=
  (abs_eval_le_coeffL1 _ p hp).trans (coeffL1_pderiv_le P k)

theorem abs_dirD_le (P : BasePoly) (W p : Fin 3 → ℝ) (hp : ∀ i, |p i| ≤ 1) :
    |dirD W P p| ≤ (|W 0| + |W 1| + |W 2|) * (P.totalDegree * coeffL1 P) := by
  unfold dirD
  have h0 := abs_eval_pderiv_le_cube P p hp 0
  have h1 := abs_eval_pderiv_le_cube P p hp 1
  have h2 := abs_eval_pderiv_le_cube P p hp 2
  calc
    |W 0 * eval p (pderiv 0 P) + W 1 * eval p (pderiv 1 P) + W 2 * eval p (pderiv 2 P)| ≤
        |W 0| * |eval p (pderiv 0 P)| + |W 1| * |eval p (pderiv 1 P)| +
          |W 2| * |eval p (pderiv 2 P)| := by
      rw [← abs_mul, ← abs_mul, ← abs_mul]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      have := abs_nonneg (W 0); have := abs_nonneg (W 1); have := abs_nonneg (W 2)
      nlinarith

theorem frX_l1 {p : Fin 3 → ℝ} (hp : ∀ i, |p i| ≤ 1) :
    |frX p 0| + |frX p 1| + |frX p 2| ≤ 2 := by
  simp only [frX, Matrix.cons_val, abs_one, abs_zero, abs_neg]; linarith [hp 1]

theorem frZ_l1 {p : Fin 3 → ℝ} (hp : ∀ i, |p i| ≤ 1) :
    |frZ p 0| + |frZ p 1| + |frZ p 2| ≤ 2 := by
  simp only [frZ, Matrix.cons_val, abs_one, abs_zero]; linarith [hp 0]

theorem l1dist_sum (x y : Fin 3 → ℝ) : ∑ i, |x i - y i| = l1dist x y := by
  simp [l1dist, Fin.sum_univ_three]

/-- Lipschitz bound in the `ℓ¹` distance for a polynomial of degree at most `D`. -/
theorem abs_eval_sub_le_l1 (P : BasePoly) (D : ℕ) (hP : P.totalDegree ≤ D) (x y : Fin 3 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    |eval x P - eval y P| ≤ D * coeffL1 P * l1dist x y := by
  have h := abs_eval_sub_eval_le P x y hx hy
  rw [l1dist_sum] at h
  have hd : (P.totalDegree : ℝ) ≤ D := by exact_mod_cast hP
  have hl : 0 ≤ l1dist x y := by unfold l1dist; positivity
  calc _ ≤ _ := h
    _ ≤ D * coeffL1 P * l1dist x y := by
      gcongr
      exact coeffL1_nonneg P

/-- The Remez constants for degree `D` at density `Λ⁻¹`. -/
def remezC (D : ℕ) (Λ : ℝ) : ℝ := (32 * ((D : ℝ) + 1) * Λ) ^ (3 * D)

theorem remez_cube (D : ℕ) (P : BasePoly) (hP : P.totalDegree ≤ D) (E : Set (Fin 3 → ℝ))
    (Λ V : ℝ) (hΛ : 1 ≤ Λ) (hV : 0 ≤ V) (hE : E ⊆ Icc (0 : Fin 3 → ℝ) 1)
    (hvol : ENNReal.ofReal Λ⁻¹ ≤ volume E) (hbd : ∀ z ∈ E, |eval z P| ≤ V) :
    ∀ z ∈ Icc (0 : Fin 3 → ℝ) 1, |eval z P| ≤ remezC D Λ * V := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have h := Submission.Lib.K4PolynomialRemezThree.polynomial_remez_fin3 D P hP E
    (inv_pos.mpr hΛ0) (inv_le_one_of_one_le₀ hΛ) hV hE hvol hbd
  intro z hz
  have e : 32 * ((D : ℝ) + 1) / Λ⁻¹ = 32 * ((D : ℝ) + 1) * Λ := by field_simp
  simpa only [remezC, e] using h z hz

section Witness

variable (α : ℝ) (β γ : BasePoly)

/-- The coefficient mass of the six frame components. -/
def sffMass : ℝ :=
  coeffL1 (cXX α β γ) + coeffL1 (cXZ α β γ) + coeffL1 (cZZ α β γ) +
    coeffL1 (cXY α β γ) + coeffL1 (cZY α β γ) + coeffL1 (cYY α β γ)

theorem sffMass_nonneg : 0 ≤ sffMass α β γ := by
  unfold sffMass
  have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cXZ α β γ)
  have := coeffL1_nonneg (cZZ α β γ); have := coeffL1_nonneg (cXY α β γ)
  have := coeffL1_nonneg (cZY α β γ); have := coeffL1_nonneg (cYY α β γ)
  linarith

variable (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

set_option maxHeartbeats 4000000 in
/-- One witness line gives the horizontal quadratic in its velocity at a nearby base point,
up to the contact and mesh errors measured by the coefficient mass. -/
theorem witness_theta (Λ ε ρ : ℝ) (b : Fin 6 → ℝ) (σ : ℝ) (p : Fin 3 → ℝ)
    (hΛ : 1 ≤ Λ) (hα : |2 * α| ≤ Λ)
    (hfit : ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hPc : lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hp : p ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hcon : |b 4 + b 0| ≤ ε) (hε1 : ε ≤ 1) (hvel : |b 3| ≤ Λ)
    (hd : l1dist (lineP b σ) p ≤ ρ) :
    |eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * b 3 + eval p (cZZ α β γ) * b 3 ^ 2| ≤
      200 * Λ ^ 3 + 16 * (ε + ρ) * Λ ^ 2 * sffMass α β γ := by
  set P := lineP b σ
  have hP1 : ∀ i, |P i| ≤ 1 := abs_le_one_of_mem_cube hPc
  have hp1 : ∀ i, |p i| ≤ 1 := abs_le_one_of_mem_cube hp
  have hΛ0 : 0 ≤ Λ := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hcon
  have hρ0 : 0 ≤ ρ := by
    refine le_trans ?_ hd; unfold l1dist; positivity
  set M := sffMass α β γ
  have hM0 : 0 ≤ M := sffMass_nonneg α β γ
  -- the line bound at `P` and the frame decomposition of its direction
  have hline := sff_line_bound α β γ hβ hγ b Λ hΛ0 hα hfit σ hσ
  rw [sffB_lineV _ _ _ _ _ _ (hessAt_symm γ P) b σ] at hline
  rw [← sffAt, ← sffAt, ← sffAt, ← sffAt, ← sffAt, ← sffAt, ← eval_cXX, ← eval_cXZ,
    ← eval_cZZ, ← eval_cXY, ← eval_cZY, ← eval_cYY] at hline
  -- coefficient-mass bounds at cube points
  have hm : ∀ (Q : BasePoly), coeffL1 Q ≤ M → ∀ q : Fin 3 → ℝ, (∀ i, |q i| ≤ 1) →
      |eval q Q| ≤ M := fun Q hQ q hq => (abs_eval_le_coeffL1 Q q hq).trans hQ
  have hXX : coeffL1 (cXX α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXZ α β γ); have := coeffL1_nonneg (cZZ α β γ)
    have := coeffL1_nonneg (cXY α β γ); have := coeffL1_nonneg (cZY α β γ)
    have := coeffL1_nonneg (cYY α β γ); linarith
  have hXZ : coeffL1 (cXZ α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cZZ α β γ)
    have := coeffL1_nonneg (cXY α β γ); have := coeffL1_nonneg (cZY α β γ)
    have := coeffL1_nonneg (cYY α β γ); linarith
  have hZZ : coeffL1 (cZZ α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cXZ α β γ)
    have := coeffL1_nonneg (cXY α β γ); have := coeffL1_nonneg (cZY α β γ)
    have := coeffL1_nonneg (cYY α β γ); linarith
  have hXY : coeffL1 (cXY α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cXZ α β γ)
    have := coeffL1_nonneg (cZZ α β γ); have := coeffL1_nonneg (cZY α β γ)
    have := coeffL1_nonneg (cYY α β γ); linarith
  have hZY : coeffL1 (cZY α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cXZ α β γ)
    have := coeffL1_nonneg (cZZ α β γ); have := coeffL1_nonneg (cXY α β γ)
    have := coeffL1_nonneg (cYY α β γ); linarith
  have hYY : coeffL1 (cYY α β γ) ≤ M := by
    unfold M sffMass
    have := coeffL1_nonneg (cXX α β γ); have := coeffL1_nonneg (cXZ α β γ)
    have := coeffL1_nonneg (cZZ α β γ); have := coeffL1_nonneg (cXY α β γ)
    have := coeffL1_nonneg (cZY α β γ); linarith
  set e := b 4 + b 0
  set v := b 3
  have hv : |v| ≤ Λ := hvel
  -- the horizontal quadratic at `P`
  have hθP : |eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ)| ≤
      200 * Λ ^ 3 + (2 * ε * (1 + Λ) + ε ^ 2) * M := by
    have h1 : |2 * e * (eval P (cXY α β γ) + v * eval P (cZY α β γ))| ≤ 2 * ε * (1 + Λ) * M := by
      rw [abs_mul, abs_mul, abs_two]
      have hb1 := hm _ hXY P hP1
      have hb2 := hm _ hZY P hP1
      have : |eval P (cXY α β γ) + v * eval P (cZY α β γ)| ≤ (1 + Λ) * M := by
        calc _ ≤ |eval P (cXY α β γ)| + |v| * |eval P (cZY α β γ)| := by
                rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ M + Λ * M := by gcongr
          _ = (1 + Λ) * M := by ring
      calc 2 * |e| * |eval P (cXY α β γ) + v * eval P (cZY α β γ)| ≤ 2 * ε * ((1 + Λ) * M) := by
            gcongr
        _ = _ := by ring
    have h2 : |e ^ 2 * eval P (cYY α β γ)| ≤ ε ^ 2 * M := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hcon 2) (hm _ hYY P hP1)
        (abs_nonneg _) (by positivity)
    have key : eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ) =
        (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ) +
          2 * e * (eval P (cXY α β γ) + v * eval P (cZY α β γ)) +
          e ^ 2 * eval P (cYY α β γ)) -
        2 * e * (eval P (cXY α β γ) + v * eval P (cZY α β γ)) - e ^ 2 * eval P (cYY α β γ) := by
      ring
    rw [key]
    calc _ ≤ |eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ) +
          2 * e * (eval P (cXY α β γ) + v * eval P (cZY α β γ)) +
          e ^ 2 * eval P (cYY α β γ)| +
          |2 * e * (eval P (cXY α β γ) + v * eval P (cZY α β γ))| +
          |e ^ 2 * eval P (cYY α β γ)| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ 200 * Λ ^ 3 + 2 * ε * (1 + Λ) * M + ε ^ 2 * M := by linarith
      _ = _ := by ring
  -- transfer from `P` to `p`
  have hl : ∀ Q : BasePoly, Q.totalDegree ≤ 4 → coeffL1 Q ≤ M →
      |eval p Q - eval P Q| ≤ 4 * M * ρ := by
    intro Q hQ hQM
    have h := abs_eval_sub_le_l1 Q 4 hQ p P hp1 hP1
    have hsym : l1dist p P = l1dist P p := by
      simp only [l1dist, abs_sub_comm]
    rw [hsym] at h
    calc _ ≤ _ := h
      _ ≤ 4 * M * ρ := by
        have := coeffL1_nonneg Q
        have := (show (0 : ℝ) ≤ l1dist P p by unfold l1dist; positivity)
        push_cast
        nlinarith
  have hdeg : ∀ U V : Fin 3 → BasePoly, (∀ i, (U i).totalDegree ≤ 1) →
      (∀ i, (V i).totalDegree ≤ 1) → (sffBP α β γ U V).totalDegree ≤ 4 :=
    fun U V hU hV => (sffBP_degree α β γ hβ hγ U V 1 1 hU hV).trans le_rfl
  have dXX : |eval p (cXX α β γ) - eval P (cXX α β γ)| ≤ 4 * M * ρ :=
    hl _ (hdeg _ _ frXP_degree frXP_degree) hXX
  have dXZ : |eval p (cXZ α β γ) - eval P (cXZ α β γ)| ≤ 4 * M * ρ :=
    hl _ (hdeg _ _ frXP_degree frZP_degree) hXZ
  have dZZ : |eval p (cZZ α β γ) - eval P (cZZ α β γ)| ≤ 4 * M * ρ :=
    hl _ (hdeg _ _ frZP_degree frZP_degree) hZZ
  have hv2 : v ^ 2 ≤ Λ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have htr : |(eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * v + eval p (cZZ α β γ) * v ^ 2) -
      (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ))| ≤
      16 * Λ ^ 2 * M * ρ := by
    have e1 : (eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * v + eval p (cZZ α β γ) * v ^ 2) -
        (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ)) =
        (eval p (cXX α β γ) - eval P (cXX α β γ)) +
          2 * v * (eval p (cXZ α β γ) - eval P (cXZ α β γ)) +
          v ^ 2 * (eval p (cZZ α β γ) - eval P (cZZ α β γ)) := by ring
    rw [e1]
    have hMρ : 0 ≤ M * ρ := mul_nonneg hM0 hρ0
    calc _ ≤ |eval p (cXX α β γ) - eval P (cXX α β γ)| +
          2 * |v| * |eval p (cXZ α β γ) - eval P (cXZ α β γ)| +
          v ^ 2 * |eval p (cZZ α β γ) - eval P (cZZ α β γ)| := by
          have h1 := abs_add_le ((eval p (cXX α β γ) - eval P (cXX α β γ)) +
            2 * v * (eval p (cXZ α β γ) - eval P (cXZ α β γ)))
            (v ^ 2 * (eval p (cZZ α β γ) - eval P (cZZ α β γ)))
          have h2 := abs_add_le (eval p (cXX α β γ) - eval P (cXX α β γ))
            (2 * v * (eval p (cXZ α β γ) - eval P (cXZ α β γ)))
          have h3 : |2 * v * (eval p (cXZ α β γ) - eval P (cXZ α β γ))| =
              2 * |v| * |eval p (cXZ α β γ) - eval P (cXZ α β γ)| := by
            rw [abs_mul, abs_mul, abs_two]
          have h4 : |v ^ 2 * (eval p (cZZ α β γ) - eval P (cZZ α β γ))| =
              v ^ 2 * |eval p (cZZ α β γ) - eval P (cZZ α β γ)| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg v)]
          linarith
      _ ≤ 4 * M * ρ + 2 * Λ * (4 * M * ρ) + Λ ^ 2 * (4 * M * ρ) := by
          gcongr
      _ ≤ 16 * Λ ^ 2 * M * ρ := by
          have h1 : (1 : ℝ) ≤ Λ ^ 2 := by nlinarith
          have h2 : Λ ≤ Λ ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hMρ, mul_le_mul_of_nonneg_right h2 hMρ]
  have hfin : (2 * ε * (1 + Λ) + ε ^ 2) * M + 16 * Λ ^ 2 * M * ρ ≤
      16 * (ε + ρ) * Λ ^ 2 * M := by
    have hε2 : ε ^ 2 ≤ ε := by
      have := mul_le_mul_of_nonneg_left hε1 hε0
      rw [pow_two]; linarith
    have h1 : (1 : ℝ) ≤ Λ ^ 2 := by nlinarith
    have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
    have hA : 2 * ε * (1 + Λ) + ε ^ 2 ≤ 16 * ε * Λ ^ 2 := by
      have e1 := mul_le_mul_of_nonneg_left h1 hε0
      have e2 := mul_le_mul_of_nonneg_left hΛ2 hε0
      nlinarith
    calc (2 * ε * (1 + Λ) + ε ^ 2) * M + 16 * Λ ^ 2 * M * ρ ≤
        16 * ε * Λ ^ 2 * M + 16 * Λ ^ 2 * M * ρ := by gcongr
      _ = 16 * (ε + ρ) * Λ ^ 2 * M := by ring
  calc _ ≤ |eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ)| +
        |(eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * v + eval p (cZZ α β γ) * v ^ 2) -
          (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ))| := by
        have := abs_add_le (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) +
          v ^ 2 * eval P (cZZ α β γ))
          ((eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * v + eval p (cZZ α β γ) * v ^ 2) -
          (eval P (cXX α β γ) + 2 * v * eval P (cXZ α β γ) + v ^ 2 * eval P (cZZ α β γ)))
        simpa [add_sub_cancel] using this
    _ ≤ 200 * Λ ^ 3 + (2 * ε * (1 + Λ) + ε ^ 2) * M + 16 * Λ ^ 2 * M * ρ := by linarith
    _ ≤ _ := by linarith

end Witness

section Budget

/-- A coefficient-control constant for base polynomials of degree at most four. -/
def CoefCtrl (Cs : ℝ) : Prop :=
  ∀ Q : BasePoly, Q.totalDegree ≤ 4 → ∀ V : ℝ, 0 ≤ V →
    (∀ x ∈ Icc (0 : Fin 3 → ℝ) 1, |eval x Q| ≤ V) → coeffL1 Q ≤ Cs * V

theorem exists_coefCtrl : ∃ Cs : ℝ, 0 < Cs ∧ CoefCtrl Cs := by
  obtain ⟨C, hC, h⟩ := exists_coeffL1_bound_on_unit_cube (n := 3) 4
  exact ⟨C, hC, fun Q hQ V hV hb => h Q hQ V hV hb⟩

/-- The discriminant budget. -/
def discBudget (Cs Λ : ℝ) : ℝ := 6 * Cs * remezC 4 Λ * Λ ^ 2

/-- One recovery step's gain. -/
def stepGain (Cs Λ : ℝ) : ℝ := remezC 4 Λ * (24 + 32 * Cs) * discBudget Cs Λ * Λ ^ 2

/-- The total amplification of the horizontal witness bound. -/
def sffKappa (Cs Λ : ℝ) : ℝ :=
  remezC 4 Λ * (32 * Λ ^ 4) * (1 + stepGain Cs Λ + stepGain Cs Λ ^ 2)

theorem remezC_nonneg (D : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ remezC D Λ := by
  unfold remezC; positivity

theorem discBudget_nonneg {Cs Λ : ℝ} (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ) : 0 ≤ discBudget Cs Λ := by
  unfold discBudget; have := remezC_nonneg 4 hΛ; positivity

theorem stepGain_nonneg {Cs Λ : ℝ} (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ) : 0 ≤ stepGain Cs Λ := by
  unfold stepGain; have := remezC_nonneg 4 hΛ; have := discBudget_nonneg hCs hΛ; positivity

theorem sffKappa_nonneg {Cs Λ : ℝ} (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ) : 0 ≤ sffKappa Cs Λ := by
  unfold sffKappa; have := remezC_nonneg 4 hΛ; have := stepGain_nonneg hCs hΛ; positivity

end Budget

section Disc

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

set_option maxHeartbeats 4000000 in
/-- The discriminant's coefficients are bounded from the line data, by absorption. -/
theorem disc_coeff_budget (Cs Λ ρ : ℝ) (S : Set (Fin 6 → ℝ)) (E : Set (Fin 3 → ℝ))
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ) (hα : |2 * α| ≤ Λ) (hρ : 0 ≤ ρ)
    (hfit : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hcube : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1) (hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E)
    (hw : ∀ p ∈ E, ∃ b ∈ S, ∃ σ ∈ Icc (0 : ℝ) 1, l1dist (lineP b σ) p ≤ ρ)
    (hs1 : 4 * Cs * remezC 4 Λ * ρ ≤ 1) :
    coeffL1 (discP α β γ) ≤ discBudget Cs Λ := by
  set D := discP α β γ
  set dd := coeffL1 D
  have hdd0 : 0 ≤ dd := coeffL1_nonneg D
  have hDdeg : D.totalDegree ≤ 2 := discP_degree α β γ hβ hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hαK : |α| ≤ Λ / 2 := by
    have : |2 * α| = 2 * |α| := by rw [abs_mul, abs_two]
    linarith
  -- bound at line points
  have hline : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, |eval (lineP b σ) D| ≤ 3 * Λ ^ 2 := by
    intro b hb σ hσ
    rw [eval_discP, discV_line]
    obtain ⟨hv, hd⟩ := hfit b hb σ hσ
    have h1 : |testDer α β b σ ^ 2| ≤ Λ ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have h2 : |4 * α * testVal α β γ b σ| ≤ 2 * Λ ^ 2 := by
      rw [abs_mul, abs_mul]
      have : |(4 : ℝ)| = 4 := by norm_num
      rw [this]
      have := abs_nonneg α
      nlinarith [abs_nonneg (testVal α β γ b σ)]
    calc _ ≤ |testDer α β b σ ^ 2| + |4 * α * testVal α β γ b σ| := abs_sub _ _
      _ ≤ 3 * Λ ^ 2 := by linarith
  -- bound on `E`
  have hE : ∀ p ∈ E, |eval p D| ≤ 3 * Λ ^ 2 + 2 * dd * ρ := by
    intro p hp
    obtain ⟨b, hb, σ, hσ, hd⟩ := hw p hp
    have hP1 := abs_le_one_of_mem_cube (hcube b hb σ hσ)
    have hp1 := abs_le_one_of_mem_cube (hEc hp)
    have hl := abs_eval_sub_le_l1 D 2 hDdeg p (lineP b σ) hp1 hP1
    have hsym : l1dist p (lineP b σ) = l1dist (lineP b σ) p := by simp only [l1dist, abs_sub_comm]
    rw [hsym] at hl
    have hl' : |eval p D - eval (lineP b σ) D| ≤ 2 * dd * ρ := by
      calc _ ≤ _ := hl
        _ ≤ 2 * dd * ρ := by
          push_cast
          exact mul_le_mul_of_nonneg_left hd (by positivity)
    have := hline b hb σ hσ
    calc |eval p D| = |(eval p D - eval (lineP b σ) D) + eval (lineP b σ) D| := by ring_nf
      _ ≤ |eval p D - eval (lineP b σ) D| + |eval (lineP b σ) D| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hcubeD := remez_cube 4 D (hDdeg.trans (by norm_num)) E Λ (3 * Λ ^ 2 + 2 * dd * ρ) hΛ
    (by positivity) hEc hEv hE
  have hcoef := hCs D (hDdeg.trans (by norm_num)) _
    (mul_nonneg (remezC_nonneg 4 hΛ0) (by positivity)) hcubeD
  -- absorption
  have hR := remezC_nonneg 4 hΛ0
  have hkey : dd ≤ Cs * remezC 4 Λ * (3 * Λ ^ 2) + (2 * Cs * remezC 4 Λ * ρ) * dd := by
    calc dd ≤ Cs * (remezC 4 Λ * (3 * Λ ^ 2 + 2 * dd * ρ)) := hcoef
      _ = _ := by ring
  have hhalf : (2 * Cs * remezC 4 Λ * ρ) * dd ≤ dd / 2 := by
    have : 2 * Cs * remezC 4 Λ * ρ ≤ 1 / 2 := by linarith
    nlinarith
  unfold discBudget
  linarith

set_option maxHeartbeats 4000000 in
/-- The discriminant is at least `Λ⁻²/4` on the witness set in the low-curvature regime. -/
theorem disc_lower_on_witness (Cs Λ ρ : ℝ) (b : Fin 6 → ℝ) (σ : ℝ) (p : Fin 3 → ℝ)
    (hΛ : 1 ≤ Λ) (hαs : |α| * (8 * Λ ^ 3) ≤ 1) (hρ : 0 ≤ ρ)
    (hfitv : |testVal α β γ b σ| ≤ Λ) (hev : Λ⁻¹ ≤ |testDer α β b σ|)
    (hPc : lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1) (hp : p ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hd : l1dist (lineP b σ) p ≤ ρ)
    (hdd : coeffL1 (discP α β γ) ≤ discBudget Cs Λ)
    (hs2 : 8 * discBudget Cs Λ * ρ * Λ ^ 2 ≤ 1) :
    (Λ ^ 2)⁻¹ / 4 ≤ eval p (discP α β γ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hDdeg : (discP α β γ).totalDegree ≤ 2 := discP_degree α β γ hβ hγ
  have hP1 := abs_le_one_of_mem_cube hPc
  have hp1 := abs_le_one_of_mem_cube hp
  -- value at the event
  have hev2 : (Λ ^ 2)⁻¹ ≤ testDer α β b σ ^ 2 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hΛ0.le) hev 2
    rw [inv_pow, sq_abs] at h
    exact h
  have hsmall : |4 * α * testVal α β γ b σ| ≤ (Λ ^ 2)⁻¹ / 2 := by
    rw [abs_mul, abs_mul]
    have h4 : |(4 : ℝ)| = 4 := by norm_num
    rw [h4]
    have hα0 := abs_nonneg α
    have hαb : |α| ≤ 1 / (8 * Λ ^ 3) := (le_div_iff₀ (by positivity)).mpr hαs
    calc 4 * |α| * |testVal α β γ b σ| ≤ 4 * (1 / (8 * Λ ^ 3)) * Λ := by gcongr
      _ = (Λ ^ 2)⁻¹ / 2 := by field_simp; ring
  have hP : (Λ ^ 2)⁻¹ / 2 ≤ eval (lineP b σ) (discP α β γ) := by
    rw [eval_discP, discV_line]
    have := le_abs_self (4 * α * testVal α β γ b σ)
    linarith
  -- transfer to `p`
  have hl := abs_eval_sub_le_l1 (discP α β γ) 2 hDdeg p (lineP b σ) hp1 hP1
  have hsym : l1dist p (lineP b σ) = l1dist (lineP b σ) p := by simp only [l1dist, abs_sub_comm]
  rw [hsym] at hl
  have hdd0 : 0 ≤ coeffL1 (discP α β γ) := coeffL1_nonneg _
  have hl0 : 0 ≤ l1dist (lineP b σ) p := by unfold l1dist; positivity
  have hl' : |eval p (discP α β γ) - eval (lineP b σ) (discP α β γ)| ≤
      2 * discBudget Cs Λ * ρ := by
    calc _ ≤ _ := hl
      _ ≤ 2 * discBudget Cs Λ * ρ := by
        push_cast
        have := mul_le_mul hdd hd hl0 (hdd0.trans hdd)
        nlinarith
  have hq : 2 * discBudget Cs Λ * ρ ≤ (Λ ^ 2)⁻¹ / 4 := by
    have e : 2 * discBudget Cs Λ * ρ = (8 * discBudget Cs Λ * ρ * Λ ^ 2) * ((Λ ^ 2)⁻¹ / 4) := by
      field_simp; ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) hs2
  have := neg_abs_le (eval p (discP α β γ) - eval (lineP b σ) (discP α β γ))
  linarith

end Disc

/-- A cube bound on a polynomial of degree at most four controls its directional derivatives
along vectors of `ℓ¹` length at most two, at cube points. -/
theorem dirD_bound_of_cube (Cs : ℝ) (hCs : CoefCtrl Cs) (Q : BasePoly) (hQ : Q.totalDegree ≤ 4)
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ x ∈ Icc (0 : Fin 3 → ℝ) 1, |eval x Q| ≤ V)
    (W p : Fin 3 → ℝ) (hW : |W 0| + |W 1| + |W 2| ≤ 2) (hp : p ∈ Icc (0 : Fin 3 → ℝ) 1) :
    |dirD W Q p| ≤ 8 * Cs * V := by
  have hc := hCs Q hQ V hV hb
  have h := abs_dirD_le Q W p (abs_le_one_of_mem_cube hp)
  have hdeg : (Q.totalDegree : ℝ) ≤ 4 := by exact_mod_cast hQ
  have hc0 := coeffL1_nonneg Q
  have hW0 : 0 ≤ |W 0| + |W 1| + |W 2| := by positivity
  calc _ ≤ _ := h
    _ ≤ 2 * (4 * (Cs * V)) := by
      apply mul_le_mul hW (mul_le_mul hdeg hc hc0 (by norm_num)) (by positivity) (by norm_num)
    _ = 8 * Cs * V := by ring

section Chain

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

theorem cXX_degree : (cXX α β γ).totalDegree ≤ 4 :=
  sffBP_degree α β γ hβ hγ _ _ 1 1 frXP_degree frXP_degree
theorem cXZ_degree : (cXZ α β γ).totalDegree ≤ 4 :=
  sffBP_degree α β γ hβ hγ _ _ 1 1 frXP_degree frZP_degree
theorem cZZ_degree : (cZZ α β γ).totalDegree ≤ 4 :=
  sffBP_degree α β γ hβ hγ _ _ 1 1 frZP_degree frZP_degree
theorem cXY_degree : (cXY α β γ).totalDegree ≤ 4 :=
  (sffBP_degree α β γ hβ hγ _ _ 1 0 frXP_degree frYP_degree).trans (by norm_num)
theorem cZY_degree : (cZY α β γ).totalDegree ≤ 4 :=
  (sffBP_degree α β γ hβ hγ _ _ 1 0 frZP_degree frYP_degree).trans (by norm_num)
theorem cYY_degree : (cYY α β γ).totalDegree ≤ 4 :=
  (sffBP_degree α β γ hβ hγ _ _ 0 0 frYP_degree frYP_degree).trans (by norm_num)

set_option maxHeartbeats 8000000 in
/-- One recovery step: a component determined by a recovery identity from two bounded
components is bounded by the step gain on the cube. -/
theorem recovery_step (Cs Λ : ℝ) (E : Set (Fin 3 → ℝ))
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ)
    (hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1) (hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E)
    (hdd : coeffL1 (discP α β γ) ≤ discBudget Cs Λ)
    (hDlow : ∀ p ∈ E, (Λ ^ 2)⁻¹ / 4 ≤ eval p (discP α β γ))
    (A B : BasePoly) (hA : A.totalDegree ≤ 4) (hB : B.totalDegree ≤ 4)
    (H : ℝ) (hH0 : 0 ≤ H)
    (bA : ∀ x ∈ Icc (0 : Fin 3 → ℝ) 1, |eval x A| ≤ H)
    (bB : ∀ x ∈ Icc (0 : Fin 3 → ℝ) 1, |eval x B| ≤ H)
    (Q : BasePoly) (hQ : Q.totalDegree ≤ 4) (c : ℝ) (hc : 4 ≤ c)
    (hid : ∀ p, c * eval p (discP α β γ) * eval p Q =
      3 * (eval p A * dirD (frZ p) (discP α β γ) p - eval p B * dirD (frX p) (discP α β γ) p) -
        2 * eval p (discP α β γ) * (dirD (frZ p) A p - dirD (frX p) B p)) :
    ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |eval p Q| ≤ stepGain Cs Λ * H := by
  have hΛ0 : 0 < Λ := by linarith
  set dB := discBudget Cs Λ with hdBdef
  have hdB0 : 0 ≤ dB := discBudget_nonneg hCs0.le hΛ0.le
  have hDdeg : (discP α β γ).totalDegree ≤ 2 := discP_degree α β γ hβ hγ
  have hDcube : ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |eval p (discP α β γ)| ≤ dB := fun p hp =>
    (abs_eval_le_coeffL1 _ p (abs_le_one_of_mem_cube hp)).trans hdd
  have hDdir : ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, ∀ W : Fin 3 → ℝ, |W 0| + |W 1| + |W 2| ≤ 2 →
      |dirD W (discP α β γ) p| ≤ 4 * dB := by
    intro p hp W hW
    have h := abs_dirD_le (discP α β γ) W p (abs_le_one_of_mem_cube hp)
    have hdeg : ((discP α β γ).totalDegree : ℝ) ≤ 2 := by exact_mod_cast hDdeg
    have hc0 := coeffL1_nonneg (discP α β γ)
    calc _ ≤ _ := h
      _ ≤ 2 * (2 * dB) := mul_le_mul hW (mul_le_mul hdeg hdd hc0 (by norm_num))
          (by positivity) (by norm_num)
      _ = 4 * dB := by ring
  have hE : ∀ p ∈ E, |eval p Q| ≤ (24 + 32 * Cs) * dB * Λ ^ 2 * H := by
    intro p hp
    have hpc := hEc hp
    have hp1 := abs_le_one_of_mem_cube hpc
    have e1 := bA p hpc
    have e2 := bB p hpc
    have e3 := hDdir p hpc _ (frZ_l1 hp1)
    have e4 := hDdir p hpc _ (frX_l1 hp1)
    have e5 := hDcube p hpc
    have e6 := dirD_bound_of_cube Cs hCs A hA H hH0 bA _ p (frZ_l1 hp1) hpc
    have e7 := dirD_bound_of_cube Cs hCs B hB H hH0 bB _ p (frX_l1 hp1) hpc
    have f1 : |eval p A * dirD (frZ p) (discP α β γ) p| ≤ H * (4 * dB) := by
      rw [abs_mul]; exact mul_le_mul e1 e3 (abs_nonneg _) hH0
    have f2 : |eval p B * dirD (frX p) (discP α β γ) p| ≤ H * (4 * dB) := by
      rw [abs_mul]; exact mul_le_mul e2 e4 (abs_nonneg _) hH0
    have f5 : |dirD (frZ p) A p - dirD (frX p) B p| ≤ 16 * Cs * H := by
      calc _ ≤ |dirD (frZ p) A p| + |dirD (frX p) B p| := abs_sub _ _
        _ ≤ _ := by linarith
    have f6 : |2 * eval p (discP α β γ) * (dirD (frZ p) A p - dirD (frX p) B p)| ≤
        2 * dB * (16 * Cs * H) := by
      rw [abs_mul, abs_mul, abs_two]
      have := abs_nonneg (eval p (discP α β γ))
      have := abs_nonneg (dirD (frZ p) A p - dirD (frX p) B p)
      gcongr
    have f7 : |3 * (eval p A * dirD (frZ p) (discP α β γ) p -
        eval p B * dirD (frX p) (discP α β γ) p)| ≤ 3 * (H * (4 * dB) + H * (4 * dB)) := by
      rw [abs_mul]
      have h3 : |(3 : ℝ)| = 3 := by norm_num
      rw [h3]
      have := abs_sub (eval p A * dirD (frZ p) (discP α β γ) p)
        (eval p B * dirD (frX p) (discP α β γ) p)
      linarith
    have hrhs : |c * eval p (discP α β γ) * eval p Q| ≤ (24 + 32 * Cs) * dB * H := by
      rw [hid p]
      calc _ ≤ _ := abs_sub _ _
        _ ≤ 3 * (H * (4 * dB) + H * (4 * dB)) + 2 * dB * (16 * Cs * H) := by linarith
        _ = (24 + 32 * Cs) * dB * H := by ring
    have hD := hDlow p hp
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have hDpos : 0 < eval p (discP α β γ) := lt_of_lt_of_le (by positivity) hD
    have hcD : (Λ ^ 2)⁻¹ ≤ c * eval p (discP α β γ) := by
      calc (Λ ^ 2)⁻¹ = 4 * ((Λ ^ 2)⁻¹ / 4) := by ring
        _ ≤ c * eval p (discP α β γ) := mul_le_mul hc hD (by positivity) (by linarith)
    have hmain : c * eval p (discP α β γ) * |eval p Q| ≤ (24 + 32 * Cs) * dB * H := by
      rwa [abs_mul, abs_mul, abs_of_pos hDpos, abs_of_pos (by linarith)] at hrhs
    have hfin : (Λ ^ 2)⁻¹ * |eval p Q| ≤ (24 + 32 * Cs) * dB * H :=
      (mul_le_mul_of_nonneg_right hcD (abs_nonneg _)).trans hmain
    have e : |eval p Q| = Λ ^ 2 * ((Λ ^ 2)⁻¹ * |eval p Q|) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hΛ2), one_mul]
    rw [e]
    calc Λ ^ 2 * ((Λ ^ 2)⁻¹ * |eval p Q|) ≤ Λ ^ 2 * ((24 + 32 * Cs) * dB * H) :=
          mul_le_mul_of_nonneg_left hfin hΛ2.le
      _ = _ := by ring
  have hR := remez_cube 4 Q hQ E Λ _ hΛ (by positivity) hEc hEv hE
  intro p hp
  calc |eval p Q| ≤ remezC 4 Λ * ((24 + 32 * Cs) * dB * Λ ^ 2 * H) := hR p hp
    _ = stepGain Cs Λ * H := by simp only [stepGain, hdBdef]; ring

set_option maxHeartbeats 8000000 in
/-- **The recovery chain.** Horizontal bounds `32 Λ⁴ T` on the witness set, the discriminant
budget and its lower bound there give all six frame components at most `κ T` on the cube. -/
theorem frame_bound_chain (Cs Λ T : ℝ) (E : Set (Fin 3 → ℝ))
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ) (hT : 0 ≤ T)
    (hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1) (hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E)
    (hH : ∀ p ∈ E, |eval p (cXX α β γ)| ≤ 32 * Λ ^ 4 * T ∧
      |eval p (cXZ α β γ)| ≤ 32 * Λ ^ 4 * T ∧ |eval p (cZZ α β γ)| ≤ 32 * Λ ^ 4 * T)
    (hdd : coeffL1 (discP α β γ) ≤ discBudget Cs Λ)
    (hDlow : ∀ p ∈ E, (Λ ^ 2)⁻¹ / 4 ≤ eval p (discP α β γ)) :
    ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1,
      |eval p (cXX α β γ)| ≤ sffKappa Cs Λ * T ∧ |eval p (cXZ α β γ)| ≤ sffKappa Cs Λ * T ∧
      |eval p (cZZ α β γ)| ≤ sffKappa Cs Λ * T ∧ |eval p (cXY α β γ)| ≤ sffKappa Cs Λ * T ∧
      |eval p (cZY α β γ)| ≤ sffKappa Cs Λ * T ∧ |eval p (cYY α β γ)| ≤ sffKappa Cs Λ * T := by
  have hΛ0 : 0 < Λ := by linarith
  set R := remezC 4 Λ with hRdef
  set g := stepGain Cs Λ with hgdef
  have hR0 : 0 ≤ R := remezC_nonneg 4 hΛ0.le
  have hg0 : 0 ≤ g := stepGain_nonneg hCs0.le hΛ0.le
  set H1 := R * (32 * Λ ^ 4 * T) with hH1def
  have hH1 : 0 ≤ H1 := by positivity
  have c1 : ∀ (Q : BasePoly), Q.totalDegree ≤ 4 → (∀ p ∈ E, |eval p Q| ≤ 32 * Λ ^ 4 * T) →
      ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |eval p Q| ≤ H1 := fun Q hQ hb =>
    remez_cube 4 Q hQ E Λ _ hΛ (by positivity) hEc hEv hb
  have bXX := c1 _ (cXX_degree α β γ hβ hγ) (fun p hp => (hH p hp).1)
  have bXZ := c1 _ (cXZ_degree α β γ hβ hγ) (fun p hp => (hH p hp).2.1)
  have bZZ := c1 _ (cZZ_degree α β γ hβ hγ) (fun p hp => (hH p hp).2.2)
  have bXY := recovery_step α β γ hβ hγ Cs Λ E hCs hCs0 hΛ hEc hEv hdd hDlow
    (cXX α β γ) (cXZ α β γ) (cXX_degree α β γ hβ hγ) (cXZ_degree α β γ hβ hγ) H1 hH1 bXX bXZ
    (cXY α β γ) (cXY_degree α β γ hβ hγ) 6 (by norm_num) (recover_cXY α β γ hβ hγ)
  have bZY := recovery_step α β γ hβ hγ Cs Λ E hCs hCs0 hΛ hEc hEv hdd hDlow
    (cXZ α β γ) (cZZ α β γ) (cXZ_degree α β γ hβ hγ) (cZZ_degree α β γ hβ hγ) H1 hH1 bXZ bZZ
    (cZY α β γ) (cZY_degree α β γ hβ hγ) 6 (by norm_num) (fun p => by
      rw [recover_cZY α β γ hβ hγ p]; ring)
  have hH2 : 0 ≤ g * H1 := by positivity
  have bYY := recovery_step α β γ hβ hγ Cs Λ E hCs hCs0 hΛ hEc hEv hdd hDlow
    (cXY α β γ) (cZY α β γ) (cXY_degree α β γ hβ hγ) (cZY_degree α β γ hβ hγ) (g * H1) hH2
    bXY bZY (cYY α β γ) (cYY_degree α β γ hβ hγ) 4 le_rfl (recover_cYY α β γ hβ hγ)
  have hκ : sffKappa Cs Λ * T = H1 + g * H1 + g * (g * H1) := by
    simp only [sffKappa, hH1def, hRdef, hgdef]; ring
  have hH3 : 0 ≤ g * (g * H1) := by positivity
  intro p hp
  rw [hκ]
  have a1 := bXX p hp; have a2 := bXZ p hp; have a3 := bZZ p hp
  have a4 := bXY p hp; have a5 := bZY p hp; have a6 := bYY p hp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Chain

section Main

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

set_option maxHeartbeats 8000000 in
/-- **Affine-sheet core.** Under the witness hypotheses, all six frame components of the
projected second fundamental form are bounded on the unit cube by `400 Λ³ κ`. -/
theorem sff_frame_bound (Cs Λ ε ρ : ℝ) (S : Set (Fin 6 → ℝ)) (E : Set (Fin 3 → ℝ))
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ) (hα : |2 * α| ≤ Λ)
    (hαs : |α| * (8 * Λ ^ 3) ≤ 1)
    (hfit : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hcube : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hcon : ∀ b ∈ S, |b 4 + b 0| ≤ ε) (hvel : ∀ b ∈ S, |b 3| ≤ Λ)
    (hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1) (hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E)
    (hwit : ∀ p ∈ E, ∃ b₁ ∈ S, ∃ b₂ ∈ S, ∃ b₃ ∈ S,
      ∃ σ₁ ∈ Icc (0 : ℝ) 1, ∃ σ₂ ∈ Icc (0 : ℝ) 1, ∃ σ₃ ∈ Icc (0 : ℝ) 1,
        l1dist (lineP b₁ σ₁) p ≤ ρ ∧ l1dist (lineP b₂ σ₂) p ≤ ρ ∧ l1dist (lineP b₃ σ₃) p ≤ ρ ∧
        Λ⁻¹ ≤ |b₁ 3 - b₂ 3| ∧ Λ⁻¹ ≤ |b₁ 3 - b₃ 3| ∧ Λ⁻¹ ≤ |b₂ 3 - b₃ 3| ∧
        Λ⁻¹ ≤ |testDer α β b₁ σ₁|)
    (hε1 : ε ≤ 1) (hρ : 0 ≤ ρ)
    (hs1 : 4 * Cs * remezC 4 Λ * ρ ≤ 1) (hs2 : 8 * discBudget Cs Λ * ρ * Λ ^ 2 ≤ 1)
    (hs3 : 192 * Cs * sffKappa Cs Λ * (ε + ρ) * Λ ^ 2 ≤ 1) :
    ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1,
      |eval p (cXX α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ ∧
      |eval p (cXZ α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ ∧
      |eval p (cZZ α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ ∧
      |eval p (cXY α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ ∧
      |eval p (cZY α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ ∧
      |eval p (cYY α β γ)| ≤ 400 * Λ ^ 3 * sffKappa Cs Λ := by
  have hΛ0 : 0 < Λ := by linarith
  -- the discriminant
  have hdd := disc_coeff_budget α β γ hβ hγ Cs Λ ρ S E hCs hCs0 hΛ hα hρ hfit hcube hEc hEv
    (fun p hp => by
      obtain ⟨b₁, hb₁, -, -, -, -, σ₁, hσ₁, -, -, -, -, hd, -⟩ := hwit p hp
      exact ⟨b₁, hb₁, σ₁, hσ₁, hd⟩) hs1
  have hDlow : ∀ p ∈ E, (Λ ^ 2)⁻¹ / 4 ≤ eval p (discP α β γ) := by
    intro p hp
    obtain ⟨b₁, hb₁, -, -, -, -, σ₁, hσ₁, -, -, -, -, hd, -, -, -, -, -, hev⟩ := hwit p hp
    exact disc_lower_on_witness α β γ hβ hγ Cs Λ ρ b₁ σ₁ p hΛ hαs hρ (hfit b₁ hb₁ σ₁ hσ₁).1
      hev (hcube b₁ hb₁ σ₁ hσ₁) (hEc hp) hd hdd hs2
  -- the horizontal components on the witness set
  set M := sffMass α β γ with hMdef
  have hM0 : 0 ≤ M := sffMass_nonneg α β γ
  set T := 200 * Λ ^ 3 + 16 * (ε + ρ) * Λ ^ 2 * M with hTdef
  have hε0 : 0 ≤ ε := by
    have h := hcon
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := hS; exact (abs_nonneg _).trans (h b hb)
    · -- with no lines the witness set is empty, contradicting its volume
      exfalso
      have hEempty : E = ∅ := by
        ext p; simp only [mem_empty_iff_false, iff_false]
        intro hp
        obtain ⟨b₁, hb₁, -⟩ := hwit p hp
        exact hS ⟨b₁, hb₁⟩
      rw [hEempty, measure_empty] at hEv
      have : (0 : ENNReal) < ENNReal.ofReal Λ⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hΛ0)
      exact absurd hEv (not_le.mpr this)
  have hT0 : 0 ≤ T := by positivity
  have hH : ∀ p ∈ E, |eval p (cXX α β γ)| ≤ 32 * Λ ^ 4 * T ∧
      |eval p (cXZ α β γ)| ≤ 32 * Λ ^ 4 * T ∧ |eval p (cZZ α β γ)| ≤ 32 * Λ ^ 4 * T := by
    intro p hp
    obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, σ₁, hσ₁, σ₂, hσ₂, σ₃, hσ₃, hd₁, hd₂, hd₃,
      hs12, hs13, hs23, -⟩ := hwit p hp
    have hpc := hEc hp
    have w₁ := witness_theta α β γ hβ hγ Λ ε ρ b₁ σ₁ p hΛ hα (hfit b₁ hb₁) hσ₁
      (hcube b₁ hb₁ σ₁ hσ₁) hpc (hcon b₁ hb₁) hε1 (hvel b₁ hb₁) hd₁
    have w₂ := witness_theta α β γ hβ hγ Λ ε ρ b₂ σ₂ p hΛ hα (hfit b₂ hb₂) hσ₂
      (hcube b₂ hb₂ σ₂ hσ₂) hpc (hcon b₂ hb₂) hε1 (hvel b₂ hb₂) hd₂
    have w₃ := witness_theta α β γ hβ hγ Λ ε ρ b₃ σ₃ p hΛ hα (hfit b₃ hb₃) hσ₃
      (hcube b₃ hb₃ σ₃ hσ₃) hpc (hcon b₃ hb₃) hε1 (hvel b₃ hb₃) hd₃
    set v : Fin 3 → ℝ := ![b₁ 3, b₂ 3, b₃ 3]
    have hv : ∀ i, |v i| ≤ Λ := by
      intro i; fin_cases i
      · exact hvel b₁ hb₁
      · exact hvel b₂ hb₂
      · exact hvel b₃ hb₃
    have hsep : ∀ i j, i ≠ j → Λ⁻¹ ≤ |v i - v j| := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp only [v] at hij ⊢
      all_goals first
        | exact absurd rfl hij
        | simpa using hs12
        | simpa using hs13
        | simpa using hs23
        | simpa [abs_sub_comm] using hs12
        | simpa [abs_sub_comm] using hs13
        | simpa [abs_sub_comm] using hs23
    have hval : ∀ i, |eval p (cXX α β γ) + 2 * eval p (cXZ α β γ) * v i +
        eval p (cZZ α β γ) * (v i) ^ 2| ≤ T := by
      intro i; fin_cases i
      · exact w₁
      · exact w₂
      · exact w₃
    have hint := Submission.Lib.K4HorizontalCoercivity.horizontal_quadratic_interpolation
      (eval p (cXX α β γ)) (2 * eval p (cXZ α β γ)) (eval p (cZZ α β γ)) Λ T hΛ hT0 v hv hsep
      hval
    have h2 : |2 * eval p (cXZ α β γ)| = 2 * |eval p (cXZ α β γ)| := by
      rw [abs_mul, abs_two]
    have := abs_nonneg (eval p (cXX α β γ))
    have := abs_nonneg (eval p (cXZ α β γ))
    have := abs_nonneg (eval p (cZZ α β γ))
    have hpos : 0 ≤ 32 * Λ ^ 4 * T := by positivity
    refine ⟨by linarith, by linarith, by linarith⟩
  -- the chain
  have hchain := frame_bound_chain α β γ hβ hγ Cs Λ T E hCs hCs0 hΛ hT0 hEc hEv hH hdd hDlow
  set κ := sffKappa Cs Λ with hκdef
  have hκ0 : 0 ≤ κ := sffKappa_nonneg hCs0.le hΛ0.le
  -- absorption in the coefficient mass
  have hcoef : ∀ (Q : BasePoly), Q.totalDegree ≤ 4 →
      (∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |eval p Q| ≤ κ * T) → coeffL1 Q ≤ Cs * (κ * T) :=
    fun Q hQ hb => hCs Q hQ (κ * T) (by positivity) hb
  have m1 := hcoef _ (cXX_degree α β γ hβ hγ) (fun p hp => (hchain p hp).1)
  have m2 := hcoef _ (cXZ_degree α β γ hβ hγ) (fun p hp => (hchain p hp).2.1)
  have m3 := hcoef _ (cZZ_degree α β γ hβ hγ) (fun p hp => (hchain p hp).2.2.1)
  have m4 := hcoef _ (cXY_degree α β γ hβ hγ) (fun p hp => (hchain p hp).2.2.2.1)
  have m5 := hcoef _ (cZY_degree α β γ hβ hγ) (fun p hp => (hchain p hp).2.2.2.2.1)
  have m6 := hcoef _ (cYY_degree α β γ hβ hγ) (fun p hp => (hchain p hp).2.2.2.2.2)
  have hMle : M ≤ 6 * Cs * κ * T := by
    simp only [hMdef, sffMass]; linarith
  have hsmall : 6 * Cs * κ * (16 * (ε + ρ) * Λ ^ 2) ≤ 1 / 2 := by nlinarith
  have hMbound : M ≤ 2400 * Cs * κ * Λ ^ 3 := by
    have e : 6 * Cs * κ * T = 1200 * Cs * κ * Λ ^ 3 + (6 * Cs * κ * (16 * (ε + ρ) * Λ ^ 2)) * M := by
      simp only [hTdef]; ring
    have h1 : (6 * Cs * κ * (16 * (ε + ρ) * Λ ^ 2)) * M ≤ M / 2 := by nlinarith
    linarith
  have hTbound : T ≤ 400 * Λ ^ 3 := by
    have h1 : 16 * (ε + ρ) * Λ ^ 2 * M ≤ 16 * (ε + ρ) * Λ ^ 2 * (2400 * Cs * κ * Λ ^ 3) := by
      have : 0 ≤ 16 * (ε + ρ) * Λ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hMbound this
    have h2 : 16 * (ε + ρ) * Λ ^ 2 * (2400 * Cs * κ * Λ ^ 3) =
        200 * Λ ^ 3 * (192 * Cs * κ * (ε + ρ) * Λ ^ 2) := by ring
    have h3 : 200 * Λ ^ 3 * (192 * Cs * κ * (ε + ρ) * Λ ^ 2) ≤ 200 * Λ ^ 3 := by
      have : 0 ≤ 200 * Λ ^ 3 := by positivity
      exact mul_le_of_le_one_right this hs3
    simp only [hTdef]; linarith
  have hκT : κ * T ≤ 400 * Λ ^ 3 * κ := by nlinarith
  intro p hp
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hchain p hp
  exact ⟨a1.trans hκT, a2.trans hκT, a3.trans hκT, a4.trans hκT, a5.trans hκT, a6.trans hκT⟩

end Main

end

end Submission.Lib.K4QuadraticSheetCore
