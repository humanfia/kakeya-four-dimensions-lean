/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/RobustQuadraticLines.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/RobustQuadraticLines.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.QuadraticFromLines
import Submission.Lib.K4ScalarCoreTools.Simulation.DirectionalVariation

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial MeasureTheory
open Submission.Lib.K4PolynomialPotential

/-- Four whole-line quadratic fits with sample points near a specified
physical base point. The samples need not occur at the same time. -/
def nearbyQuadraticLineFits (P : MvPolynomial (Fin 2) ℝ)
    (z : Fin 2 → ℝ) (K E τ : ℝ) : Prop :=
  ∃ (v u t : Fin 4 → ℝ) (T : Fin 4 → Polynomial ℝ),
    (∀ i, |v i| ≤ K) ∧
    (∀ i j, i ≠ j → 1 / K ≤ |v i - v j|) ∧
    (∀ i, t i ∈ Icc (-1 : ℝ) 1 ∧
      (![t i, u i + t i * v i] : Fin 2 → ℝ) ∈ Icc (-1) 1 ∧
      |t i - z 0| + |u i + t i * v i - z 1| ≤ τ ∧
      (T i).natDegree ≤ 2 ∧
      ∀ r ∈ Icc (-1 : ℝ) 1, |eval ![r, u i + r * v i] P - (T i).eval r| ≤ E)

/-- The actual line fits and their displacement errors bound every third
partial at the reference point. -/
theorem exists_third_bound_of_nearby_quadratic_lines_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K H E τ : ℝ, 1 ≤ K → 0 ≤ H → 0 ≤ E → 0 ≤ τ →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ H) →
      ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, nearbyQuadraticLineFits P z K E τ →
      ∀ i j k : Fin 2, |eval z (pderiv i (pderiv j (pderiv k P)))| ≤
        C * K ^ 6 * (E + K ^ 3 * H * τ) := by
  obtain ⟨Cline, hCline, hline⟩ := exists_third_bound_of_quadratic_fit_constant D
  obtain ⟨Cvar, hCvar, hvar⟩ := exists_directional_third_variation_constant D
  obtain ⟨Cdir, hCdir, hdir⟩ := exists_four_direction_third_constant
  refine ⟨Cdir * (Cline + Cvar), by positivity, ?_⟩
  intro P hP K H E τ hK hH hE hτ hnorm z hz hfits
  obtain ⟨v, u, t, T, hv, hsep, hdata⟩ := hfits
  let B := Cline * E + Cvar * K ^ 3 * H * τ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hthird (l : Fin 4) :
      |eval z (directionalPartial (v l)
        (directionalPartial (v l) (directionalPartial (v l) P)))| ≤ B := by
    obtain ⟨ht, hpoint, hnear, hT, hfit⟩ := hdata l
    have hsmall := hline P hP (T l) hT (u l) (v l) E hE hfit (t l) ht
    have hmove := hvar P hP K H hK hH hnorm (v l) (hv l)
      (![t l, u l + t l * v l]) hpoint z hz
    have hdist : |z 0 - (![t l, u l + t l * v l] : Fin 2 → ℝ) 0| +
        |z 1 - (![t l, u l + t l * v l] : Fin 2 → ℝ) 1| ≤ τ := by
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_sub_comm] using hnear
    have hmove' : |eval z (directionalPartial (v l)
          (directionalPartial (v l) (directionalPartial (v l) P))) -
        eval ![t l, u l + t l * v l] (directionalPartial (v l)
          (directionalPartial (v l) (directionalPartial (v l) P)))| ≤
            Cvar * K ^ 3 * H * τ :=
      hmove.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
    have htriangle := abs_add_le
      (eval z (directionalPartial (v l)
          (directionalPartial (v l) (directionalPartial (v l) P))) -
        eval ![t l, u l + t l * v l] (directionalPartial (v l)
          (directionalPartial (v l) (directionalPartial (v l) P))))
      (eval ![t l, u l + t l * v l] (directionalPartial (v l)
          (directionalPartial (v l) (directionalPartial (v l) P))))
    rw [sub_add_cancel] at htriangle
    dsimp only [B]
    linarith
  have hbudget : B ≤ (Cline + Cvar) * (E + K ^ 3 * H * τ) := by
    have hnonneg : 0 ≤ K ^ 3 * H * τ := by positivity
    have h1 := mul_nonneg hCvar.le hE
    have h2 := mul_nonneg hCline.le hnonneg
    dsimp only [B]
    nlinarith
  intro i j k
  have h := hdir P z v K B hK hB hv hsep hthird i j k
  calc
    _ ≤ Cdir * K ^ 6 * B := h
    _ ≤ Cdir * K ^ 6 * ((Cline + Cvar) * (E + K ^ 3 * H * τ)) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = (Cdir * (Cline + Cvar)) * K ^ 6 * (E + K ^ 3 * H * τ) := by ring

/-- Positive-area nearby trajectory fits recover a single actual quadratic,
with the mesh displacement paid before the Remez comparison. -/
theorem exists_quadratic_restoration_from_nearby_lines_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K H E τ η : ℝ, 1 ≤ K → 0 ≤ H → 0 ≤ E → 0 ≤ τ → 0 < η → η ≤ 1 →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ H) →
      ∀ S : Set (Fin 2 → ℝ), S ⊆ Icc (-1 : Fin 2 → ℝ) 1 →
      ENNReal.ofReal η ≤ volume S →
      (∀ z ∈ S, nearbyQuadraticLineFits P z K E τ) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ e : Fin 2 →₀ ℕ, e.degree ≤ 2 → Q.coeff e = P.coeff e) ∧
        ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P - eval z Q| ≤
          C * K ^ 6 * (64 * ((D : ℝ) + 1) / η) ^ (2 * D) *
            (E + K ^ 3 * H * τ) := by
  obtain ⟨Cjet, hCjet, hjet⟩ := exists_third_bound_of_nearby_quadratic_lines_constant D
  obtain ⟨Cquad, hCquad, hquad⟩ := exists_quadratic_truncation_constant D
  refine ⟨Cquad ^ 2 * Cjet, by positivity, ?_⟩
  intro P hP K H E τ η hK hH hE hτ hη hη1 hnorm S hS hmass hlines
  let B := Cjet * K ^ 6 * (E + K ^ 3 * H * τ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpd (R : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
      (pderiv i R).totalDegree ≤ R.totalDegree :=
    (totalDegree_pderiv_le R i).trans (Nat.sub_le _ _)
  let F := (64 * ((D : ℝ) + 1) / η) ^ (2 * D)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hthird (i j k : Fin 2) : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ F * B :=
    polynomial_remez_symmetric_two _ D
      ((hpd _ i).trans ((hpd _ j).trans ((hpd _ k).trans hP)))
      S hη hη1 hB hS hmass (fun z hz =>
        hjet P hP K H E τ hK hH hE hτ hnorm z (hS hz) (hlines z hz) i j k)
  obtain ⟨hdegree, herror⟩ := hquad 2 P hP (F * B) (mul_nonneg hF hB) hthird
  refine ⟨quadraticTruncation P, hdegree, ?_, ?_⟩
  · intro e he
    simp only [coeff_quadraticTruncation, he, ↓reduceIte]
  · intro z hz
    convert herror z hz using 1
    dsimp only [F, B]
    ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
