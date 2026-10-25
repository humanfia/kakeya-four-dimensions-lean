/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/Normalization/Atlas.lean.
Earlier provenance is preserved below.
-/
/-
Adapted from this LOT tree, o064, session x0214, commit 1213d02,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/Atlas.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.Lift

/-!
# Atlases and normalized events

The inverse of the normalization of trajectory coefficients, the normalized
event of an assignment (so that child events correspond to original ones, as
`ChartSystem.lift_valid` requires), the passage from a valid system to its
geometric part, and monotonicity of validity in the slack and format bounds.
-/
namespace Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The inverse of the normalization of trajectory coefficients. -/
noncomputable def denormCoeff (l' : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let z₀ : Fin 2 → ℝ := ![l' 0, l' 1]
  let z₁ : Fin 2 → ℝ := ![l' 3, l' 4]
  let a := F.D.mulVec z₀
  let b := F.D.mulVec z₁
  let v₀ := F.u 0 + F.q⁻¹ * b 0
  let v₁ := F.u 1 + F.q⁻¹ * b 1
  let s₃ := F.q⁻¹ * l' 5
  ![a 0 + F.c 0 + F.t₀ * F.u 0 - F.t₀ * v₀,
    a 1 + F.c 1 + F.t₀ * F.u 1 - F.t₀ * v₁,
    l' 2 - F.t₀ * s₃,
    v₀, v₁, s₃]

theorem denormCoeff_normCoeff (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Fin 6 → ℝ) :
    F.denormCoeff (F.normCoeff l) = l := by
  have hm : F.D * F.D⁻¹ = 1 := Matrix.mul_nonsing_inv F.D hD
  have h00 : F.D 0 0 * F.D⁻¹ 0 0 + F.D 0 1 * F.D⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D 0 0 * F.D⁻¹ 0 1 + F.D 0 1 * F.D⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D 1 0 * F.D⁻¹ 0 0 + F.D 1 1 * F.D⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D 1 0 * F.D⁻¹ 0 1 + F.D 1 1 * F.D⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  funext e
  fin_cases e <;> simp [denormCoeff, normCoeff, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp
  · linear_combination (l 0 - F.c 0) * h00 + (l 1 - F.c 1) * h01
  · linear_combination (l 0 - F.c 0) * h10 + (l 1 - F.c 1) * h11
  · ring
  · linear_combination (l 3 - F.u 0) * h00 + (l 4 - F.u 1) * h01
  · linear_combination (l 3 - F.u 0) * h10 + (l 4 - F.u 1) * h11


/-- The normalized event of an assignment `A₀` and an event `E`: incidences whose
original trajectory lies in `A₀`, at normalized times in `[0, 1]`, whose original
incidence lies in `E`. -/
def normEvent (A₀ : Set Trajectory) (E : Set Incidence) : Set Incidence :=
  {p | (p.1.1, F.denormCoeff p.1.2) ∈ A₀ ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ((p.1.1, F.denormCoeff p.1.2), F.t₀ + F.q * p.2) ∈ E}

theorem mem_of_mem_normEvent (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (A₀ : Set Trajectory)
    (E : Set Incidence) (l : Trajectory) (t : ℝ)
    (h : (F.normTraj l, (t - F.t₀) / F.q) ∈ F.normEvent A₀ E) : (l, t) ∈ E := by
  obtain ⟨_, _, h3⟩ := h
  have e1 : (F.normTraj l).1 = l.1 := rfl
  have e2 : F.denormCoeff (F.normTraj l).2 = l.2 := F.denormCoeff_normCoeff hq hD l.2
  have e3 : F.t₀ + F.q * ((t - F.t₀) / F.q) = t := by field_simp; ring
  rw [e1, e2, e3] at h3
  exact h3

end Frame

namespace ChartSystem

theorem Valid.geometry {W T : ℕ} {s : ChartSystem W T} {N κ fL δ : ℝ} {M D : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {E : Fin W → Set Incidence}
    {B : Fin W → ℝ} (h : s.Valid N κ fL δ M D ω ν E B) : s.Geometry N κ M D := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨h1, h2, fun b => ?_⟩
  obtain ⟨a1, a2, a3, a4, _, _, a7, _, a9, a10, _⟩ := h3 b
  exact ⟨a1, a2, a3, a4, a7, fun i => (a9 i).1, fun l hl => ⟨(a10 l hl).1, (a10 l hl).2.1⟩⟩

/-- Valid systems stay valid when the slack, the format exponent and the degree
bound are enlarged. -/
theorem Valid.mono {W T : ℕ} {s : ChartSystem W T} {N κ κ₂ fL δ : ℝ} {M M₂ D D₂ : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {E : Fin W → Set Incidence}
    {B : Fin W → ℝ} (h : s.Valid N κ fL δ M D ω ν E B) (hN : 1 ≤ N) (hκ0 : 0 < κ)
    (hκ : κ ≤ κ₂) (hM : M ≤ M₂) (hD : D ≤ D₂) (hδ : 0 ≤ δ) (hB : ∀ γ, 0 ≤ B γ) :
    s.Valid N κ₂ fL δ M₂ D₂ ω ν E B := by
  have hP : N ^ M ≤ N ^ M₂ := pow_le_pow_right₀ hN hM
  have hκ₂ : 0 < κ₂ := lt_of_lt_of_le hκ0 hκ
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.trans hP, h2, fun b => ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h3 b
    have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    refine ⟨a1, a2.trans hP, a3.trans hP, a4.trans (div_le_div_of_nonneg_right hκ hT.le), a5,
      fun e => (a6 e).trans hP, a7, a8,
      fun i => ⟨Fmt.mono (a9 i).1 hP hD, Fmt.mono (a9 i).2 hP hD⟩, fun l hl => ?_, fun p hp => ?_, ?_⟩
    · obtain ⟨b1, b2, b3⟩ := a10 l hl
      refine ⟨b1.trans hP, fun e => (b2 e).trans hP, fun t ht => ?_⟩
      obtain ⟨c1, c2, c3, c4⟩ := b3 t ht
      have hBb := hB (s.world b)
      refine ⟨c1.trans hκ, c2.trans (mul_le_mul_of_nonneg_right hκ hδ),
        c3.trans (mul_le_mul_of_nonneg_right hκ hBb), c4.trans ?_⟩
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hκ (div_nonneg (sq_nonneg _) hδ)
    · obtain ⟨b1, b2, b3, b4⟩ := a11 p hp
      exact ⟨b1, b2, b3, le_trans (div_le_div_of_nonneg_left (hB _) hκ0 hκ) b4⟩
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) a12
      apply div_le_div_of_nonneg_left _ (mul_pos hT hκ0) (mul_le_mul_of_nonneg_left hκ hT.le)
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (abs_nonneg _)
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) h4
    exact inv_anti₀ hκ0 hκ

end ChartSystem

end Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
