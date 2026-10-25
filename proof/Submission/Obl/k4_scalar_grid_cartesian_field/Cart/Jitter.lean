-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/Jitter.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_eligibility_sign_description.Families

/-!
Undoing a single common coefficient jitter in all scalar projection packets.
The transformation preserves degree, the fitting error, and the adapted norm
up to the size of the added quadratic jitter.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set
open Submission.Obl.k4_eligibility_sign_description

noncomputable section

def affineTrace (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 1

def hiddenTrace (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

def hiddenPolynomial (b : Fin 5 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (b 2) + MvPolynomial.X 0 * MvPolynomial.C (b 3) +
    MvPolynomial.X 0 ^ 2 * MvPolynomial.C (b 4)

theorem eval_hiddenPolynomial (b : Fin 5 → ℝ) (t y : ℝ) :
    MvPolynomial.eval ![t, y] (hiddenPolynomial b) = hiddenTrace b t := by
  simp [hiddenPolynomial, hiddenTrace]

theorem degree_hiddenPolynomial (b : Fin 5 → ℝ) :
    (hiddenPolynomial b).totalDegree ≤ 2 := by
  apply degree_add_le
  · apply degree_add_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- The original predictor corresponding to a fit for coefficients `b + δ`. -/
def undoJitter (P : MvPolynomial (Fin 2) ℝ) (δ : Fin 5 → ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval ![MvPolynomial.X 0,
    MvPolynomial.X 1 + MvPolynomial.C (δ 0) + MvPolynomial.X 0 * MvPolynomial.C (δ 1)] P -
      hiddenPolynomial δ

theorem degree_undoJitter (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (δ : Fin 5 → ℝ) : (undoJitter P δ).totalDegree ≤ 2 := by
  apply degree_sub_le
  · refine (degree_aeval_le P _ ?_).trans hP
    intro i
    fin_cases i
    · simp
    · apply degree_add_le
      · exact degree_add_le (by simp) (by simp)
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · exact degree_hiddenPolynomial δ

theorem eval_undoJitter (P : MvPolynomial (Fin 2) ℝ)
    (δ : Fin 5 → ℝ) (t y : ℝ) :
    MvPolynomial.eval ![t, y] (undoJitter P δ) =
      MvPolynomial.eval ![t, y + affineTrace δ t] P - hiddenTrace δ t := by
  rw [undoJitter, map_sub, eval_aeval_real, eval_hiddenPolynomial]
  congr 1
  apply congrArg (fun f : Fin 2 → ℝ => MvPolynomial.eval f P)
  funext i
  fin_cases i <;> simp [affineTrace, add_assoc]

theorem affineTrace_add (b δ : Fin 5 → ℝ) (t : ℝ) :
    affineTrace (b + δ) t = affineTrace b t + affineTrace δ t := by
  simp only [affineTrace, Pi.add_apply]
  ring

theorem hiddenTrace_add (b δ : Fin 5 → ℝ) (t : ℝ) :
    hiddenTrace (b + δ) t = hiddenTrace b t + hiddenTrace δ t := by
  simp only [hiddenTrace, Pi.add_apply]
  ring

/-- Undoing the common jitter preserves each trajectory's fitting residual exactly. -/
theorem residual_undoJitter (P : MvPolynomial (Fin 2) ℝ)
    (b δ : Fin 5 → ℝ) (t : ℝ) :
    hiddenTrace b t - MvPolynomial.eval ![t, affineTrace b t] (undoJitter P δ) =
      hiddenTrace (b + δ) t - MvPolynomial.eval ![t, affineTrace (b + δ) t] P := by
  simp only [eval_undoJitter, hiddenTrace_add, affineTrace_add]
  ring

theorem confinement_undoJitter (b δ : Fin 5 → ℝ) (u v t : ℝ) :
    affineTrace b t - (u - δ 0) - t * (v - δ 1) =
      affineTrace (b + δ) t - u - t * v := by
  simp only [affineTrace, Pi.add_apply]
  ring

theorem abs_affineTrace_le (b : Fin 5 → ℝ) {ρ : ℝ}
    (hb : ∀ i, |b i| ≤ ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |affineTrace b t| ≤ 2 * ρ := by
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  calc
    |affineTrace b t| ≤ |b 0| + |t| * |b 1| := by
      simpa only [affineTrace, abs_mul] using abs_add_le (b 0) (t * b 1)
    _ ≤ ρ + 1 * ρ := add_le_add (hb 0)
      (mul_le_mul ht' (hb 1) (abs_nonneg _) zero_le_one)
    _ = 2 * ρ := by ring

theorem abs_hiddenTrace_le (b : Fin 5 → ℝ) {ρ : ℝ}
    (hb : ∀ i, |b i| ≤ ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hiddenTrace b t| ≤ 3 * ρ := by
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht₂ : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) ht' 2).trans_eq (one_pow 2)
  calc
    |hiddenTrace b t| ≤ |b 2| + |t| * |b 3| + |t ^ 2| * |b 4| := by
      exact (abs_add_le _ _).trans (add_le_add
        (by simpa only [abs_mul] using abs_add_le (b 2) (t * b 3))
        (by rw [abs_mul]))
    _ ≤ ρ + 1 * ρ + 1 * ρ := add_le_add
      (add_le_add (hb 2) (mul_le_mul ht' (hb 3) (abs_nonneg _) zero_le_one))
      (mul_le_mul ht₂ (hb 4) (abs_nonneg _) zero_le_one)
    _ = 3 * ρ := by ring

/-- In coordinates following the corrected center, the predictor norm changes
only by the hidden-coordinate jitter. -/
theorem adapted_norm_undoJitter (P : MvPolynomial (Fin 2) ℝ) (δ : Fin 5 → ℝ)
    {u v β H ρ : ℝ} (hδ : ∀ i, |δ i| ≤ ρ)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + β * w] P| ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, (u - δ 0) + t * (v - δ 1) + β * w]
        (undoJitter P δ)| ≤ H + 3 * ρ := by
  intro t ht w hw
  rw [eval_undoJitter]
  have heq : (u - δ 0) + t * (v - δ 1) + β * w + affineTrace δ t =
      u + t * v + β * w := by simp only [affineTrace]; ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add (hP t ht w hw) (abs_hiddenTrace_le δ hδ ht))

theorem center_bound_undoJitter {u v ρ : ℝ} (δ : Fin 5 → ℝ)
    (hδ : ∀ i, |δ i| ≤ ρ) :
    |u - δ 0| + |v - δ 1| ≤ |u| + |v| + 2 * ρ := by
  have h := add_le_add (abs_sub u (δ 0)) (abs_sub v (δ 1))
  linarith [hδ 0, hδ 1]

end
end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
