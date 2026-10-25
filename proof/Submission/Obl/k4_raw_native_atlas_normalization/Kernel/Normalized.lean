/- Adapted from this LOT tree, obligation o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/Normalized.lean. Original provenance is retained below. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.Atlas

/-!
# The normalized problem of an atlas, at one sample (paper Lemma 2.13, first part)

Inverse substitution and the normalized native test `P' = P_c / δ_r` in the
coordinates `(τ, z, w)`; native bounds of normalized worlds from the chart conditions
(`ChartSystem.norm_native_bounds`, with slack `3κ` and scale `B / δ_r`); the lower
native bound from the chart's selected incidences (`Frame.normTest_lower`); the mass of
a normalized event (`Frame.prod_normEvent`: `m_c = q · ((normTraj)_* ν|_{A_c} ⊗ vol)(E'_c)`).
-/
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The normalized trajectory's inverse. -/
noncomputable def denormTraj (l : Trajectory) : Trajectory := (l.1, F.denormCoeff l.2)

/-- Original graph coordinates through normalized ones:
`t = t₀ + q τ`, `y = c + t u + D z`, `w = w`. -/
noncomputable def unsubst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C F.t₀ + C F.q * X 0,
    C (F.c 0) + (C F.t₀ + C F.q * X 0) * C (F.u 0) + C (F.D 0 0) * X 1 + C (F.D 0 1) * X 2,
    C (F.c 1) + (C F.t₀ + C F.q * X 0) * C (F.u 1) + C (F.D 1 0) * X 1 + C (F.D 1 1) * X 2,
    X 3]

theorem eval_unsubst (hq : F.q ≠ 0) (l : Trajectory) (τ : ℝ) :
    (fun i => eval (graphPoint l τ) (F.unsubst i)) =
      graphPoint (F.denormTraj l) (F.t₀ + F.q * τ) := by
  funext i
  fin_cases i <;>
    simp [unsubst, graphPoint, denormTraj, denormCoeff, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> field_simp <;> ring

theorem totalDegree_unsubst_le (i : Fin 4) : (F.unsubst i).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 4, (X i : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := fun i => deg1_X i
  have ht : (C F.t₀ + C F.q * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    deg1_add (deg1_C _) (deg1_C_mul _ (hX 0))
  fin_cases i
  · exact ht
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ ht)) (deg1_C_mul _ (hX 1)))
      (deg1_C_mul _ (hX 2))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ ht)) (deg1_C_mul _ (hX 1)))
      (deg1_C_mul _ (hX 2))
  · exact hX 3

theorem pderiv_three_unsubst_three : pderiv (3 : Fin 4) (F.unsubst 3) = 1 := by
  simp [unsubst]

theorem pderiv_three_unsubst_of_ne (j : Fin 4) (hj : j ≠ 3) :
    pderiv (3 : Fin 4) (F.unsubst j) = 0 := by
  fin_cases j <;> simp_all [unsubst, pderiv_X]

/-- The normalized native polynomial `P'(τ, z, w) = P(t, y, w) / δ`. -/
noncomputable def normTest (δ : ℝ) (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  δ⁻¹ • bind₁ F.unsubst P

theorem eval_normTest (hq : F.q ≠ 0) (δ : ℝ) (P : MvPolynomial (Fin 4) ℝ) (l : Trajectory)
    (τ : ℝ) :
    eval (graphPoint l τ) (F.normTest δ P) =
      δ⁻¹ * eval (graphPoint (F.denormTraj l) (F.t₀ + F.q * τ)) P := by
  rw [normTest, MvPolynomial.smul_eval, ← F.eval_unsubst hq l τ, eval_bind₁']

theorem pderiv_normTest (δ : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (F.normTest δ P) = F.normTest δ (pderiv 3 P) := by
  rw [normTest, normTest, Derivation.map_smul,
    pderiv_bind₁_of_diagonal F.unsubst 3 F.pderiv_three_unsubst_three
      F.pderiv_three_unsubst_of_ne]

theorem totalDegree_normTest_le (δ : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (F.normTest δ P).totalDegree ≤ P.totalDegree :=
  (totalDegree_smul_le _ _).trans (totalDegree_bind₁_le_of_le_one _ F.totalDegree_unsubst_le P)

theorem denormTraj_normTraj (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Trajectory) :
    F.denormTraj (F.normTraj l) = l := by
  simp [denormTraj, normTraj, F.denormCoeff_normCoeff hq hD]

end Frame
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel

namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

theorem normTraj_fst (l : Trajectory) : (F.normTraj l).1 = l.1 := rfl

/-- Native bounds of the normalized test along a normalized trajectory, from the
chart conditions of the parent chart on its block. -/
theorem normTest_bounds (hq : F.q ≠ 0) (hD : IsUnit F.D.det) {δ κ B : ℝ} (hδ : 0 < δ)
    (P : MvPolynomial (Fin 4) ℝ) (l : Trajectory) (τ : ℝ)
    (h1 : |eval (graphPoint l (F.t₀ + F.q * τ)) P| ≤ κ * δ)
    (h2 : |eval (graphPoint l (F.t₀ + F.q * τ)) (pderiv 3 P)| ≤ κ * B)
    (h3 : |eval (graphPoint l (F.t₀ + F.q * τ)) (pderiv 3 (pderiv 3 P))| ≤ κ * B ^ 2 / δ) :
    |eval (graphPoint (F.normTraj l) τ) (F.normTest δ P)| ≤ κ ∧
    |eval (graphPoint (F.normTraj l) τ) (pderiv 3 (F.normTest δ P))| ≤ κ * (B / δ) ∧
    |eval (graphPoint (F.normTraj l) τ) (pderiv 3 (pderiv 3 (F.normTest δ P)))| ≤
      κ * (B / δ) ^ 2 := by
  have hl : F.denormTraj (F.normTraj l) = l := F.denormTraj_normTraj hq hD l
  rw [F.pderiv_normTest, F.pderiv_normTest, F.eval_normTest hq, F.eval_normTest hq,
    F.eval_normTest hq, hl]
  have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hδi]
    calc δ⁻¹ * _ ≤ δ⁻¹ * (κ * δ) := mul_le_mul_of_nonneg_left h1 hδi.le
      _ = κ := by field_simp
  · rw [abs_mul, abs_of_pos hδi]
    calc δ⁻¹ * _ ≤ δ⁻¹ * (κ * B) := mul_le_mul_of_nonneg_left h2 hδi.le
      _ = κ * (B / δ) := by field_simp
  · rw [abs_mul, abs_of_pos hδi]
    calc δ⁻¹ * _ ≤ δ⁻¹ * (κ * B ^ 2 / δ) := mul_le_mul_of_nonneg_left h3 hδi.le
      _ = κ * (B / δ) ^ 2 := by field_simp

/-- Lower native bound of the normalized test, from the parent chart's selected
incidences. -/
theorem normTest_lower (hq : F.q ≠ 0) {δ κ B : ℝ} (hδ : 0 < δ) (P : MvPolynomial (Fin 4) ℝ)
    (l : Trajectory) (τ : ℝ)
    (h : B / κ ≤ |eval (graphPoint (F.denormTraj l) (F.t₀ + F.q * τ)) (pderiv 3 P)|) :
    B / δ / κ ≤ |eval (graphPoint l τ) (pderiv 3 (F.normTest δ P))| := by
  rw [F.pderiv_normTest, F.eval_normTest hq, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  calc B / δ / κ = δ⁻¹ * (B / κ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hδ.le)

/-- The planar point of a normalized trajectory is bounded by the chart slack, and so is
its velocity. -/
theorem norm_planar_normTraj_le (hq : 0 < F.q) {κ : ℝ} (l : Trajectory)
    (hfit : ∀ t ∈ Set.Icc F.t₀ (F.t₀ + F.q),
      ‖Matrix.toEuclideanLin F.D⁻¹ (planarPoint l t - F.c - t • F.u)‖ ≤ κ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ‖planarPoint (F.normTraj l) τ‖ ≤ κ := by
  have h := hfit (F.t₀ + F.q * τ) ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have e : (F.t₀ + F.q * τ - F.t₀) / F.q = τ := by field_simp; ring
  rw [← F.planarPoint_normTraj hq.ne' l (F.t₀ + F.q * τ), e] at h
  exact h

end Frame
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel

namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

/-- The velocity of a trajectory, as in the frozen statement. -/
def velocity (l : Trajectory) : Plane := WithLp.toLp 2 ![l.2 3, l.2 4]

theorem velocity_eq_sub (l : Trajectory) : velocity l = planarPoint l 1 - planarPoint l 0 := by
  ext i; fin_cases i <;> simp [velocity, planarPoint]

theorem norm_planar_add_velocity_le {l : Trajectory} {κ : ℝ}
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖planarPoint l τ‖ ≤ κ) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : ‖planarPoint l τ‖ + ‖velocity l‖ ≤ 3 * κ := by
  have h0 := h 0 ⟨le_rfl, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_rfl⟩
  have hv : ‖velocity l‖ ≤ ‖planarPoint l 1‖ + ‖planarPoint l 0‖ := by
    rw [velocity_eq_sub]; exact norm_sub_le _ _
  have := h τ hτ
  linarith

namespace ChartSystem

theorem timeBlock_frameOf {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    timeBlock T (s.block c) = Set.Icc (s.frameOf c).t₀ ((s.frameOf c).t₀ + (s.frameOf c).q) := by
  simp only [timeBlock, frameOf]
  congr 1
  ring

/-- Native bounds of a normalized world of an atlas, at every time of `[0, 1]`, for every
trajectory of the chart's assignment. -/
theorem norm_native_bounds {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) {κ δ B : ℝ}
    (hδ : 0 < δ) (hD : IsUnit (s.frame c).det)
    (hchart : ∀ l ∈ s.assignment c, ∀ t ∈ timeBlock T (s.block c),
      ‖Matrix.toEuclideanLin ((s.frame c)⁻¹) (planarPoint l t - s.center c - t • s.speed c)‖ ≤ κ ∧
      |MvPolynomial.eval (graphPoint l t) (s.test c)| ≤ κ * δ ∧
      |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) (s.test c))| ≤ κ * B ∧
      |MvPolynomial.eval (graphPoint l t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (s.test c)))| ≤
        κ * B ^ 2 / δ)
    (l : Trajectory) (hl : l ∈ s.assignment c) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ‖planarPoint ((s.frameOf c).normTraj l) τ‖ + ‖velocity ((s.frameOf c).normTraj l)‖ ≤
        3 * κ ∧
      |eval (graphPoint ((s.frameOf c).normTraj l) τ) ((s.frameOf c).normTest δ (s.test c))| ≤
        κ ∧
      |eval (graphPoint ((s.frameOf c).normTraj l) τ)
        (pderiv 3 ((s.frameOf c).normTest δ (s.test c)))| ≤ κ * (B / δ) ∧
      |eval (graphPoint ((s.frameOf c).normTraj l) τ)
        (pderiv 3 (pderiv 3 ((s.frameOf c).normTest δ (s.test c))))| ≤ κ * (B / δ) ^ 2 := by
  have hq := s.frameOf_q_pos c
  have hblock := s.timeBlock_frameOf c
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      (s.frameOf c).t₀ + (s.frameOf c).q * τ ∈ timeBlock T (s.block c) := by
    intro τ hτ
    rw [hblock]
    exact ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hfit : ∀ t ∈ Set.Icc (s.frameOf c).t₀ ((s.frameOf c).t₀ + (s.frameOf c).q),
      ‖Matrix.toEuclideanLin (s.frameOf c).D⁻¹
        (planarPoint l t - (s.frameOf c).c - t • (s.frameOf c).u)‖ ≤ κ := by
    intro t ht
    rw [← hblock] at ht
    exact (hchart l hl t ht).1
  obtain ⟨_, h1, h2, h3⟩ := hchart l hl _ (hmem τ hτ)
  obtain ⟨g1, g2, g3⟩ := (s.frameOf c).normTest_bounds hq.ne' hD hδ (s.test c) l τ h1 h2 h3
  refine ⟨norm_planar_add_velocity_le
    (fun τ' hτ' => (s.frameOf c).norm_planar_normTraj_le hq l hfit τ' hτ') τ hτ, g1, g2, g3⟩

end ChartSystem
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel

namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

theorem continuous_denormCoeff : Continuous F.denormCoeff := by
  unfold denormCoeff
  refine continuous_pi fun e => ?_
  fin_cases e <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> fun_prop

theorem measurable_denormTraj : Measurable F.denormTraj :=
  measurable_fst.prodMk (F.continuous_denormCoeff.measurable.comp measurable_snd)

theorem measurableSet_normEvent {A₀ : Set Trajectory} {E : Set Incidence}
    (hA : MeasurableSet A₀) (hE : MeasurableSet E) : MeasurableSet (F.normEvent A₀ E) := by
  have h1 : Measurable fun p : Incidence => F.denormTraj p.1 :=
    F.measurable_denormTraj.comp measurable_fst
  have h2 : Measurable fun p : Incidence => (F.denormTraj p.1, F.t₀ + F.q * p.2) :=
    h1.prodMk (measurable_const.add (measurable_const.mul measurable_snd))
  exact (h1 hA).inter ((measurable_snd measurableSet_Icc).inter (h2 hE))

/-- An event inside the chart's assignment and block is the lift of its normalized event,
so its mass is `q` times the normalized mass. -/
theorem prod_normEvent (hq : 0 < F.q) (hD : IsUnit F.D.det) (ν : Measure Trajectory)
    [SFinite ν] {A₀ : Set Trajectory} {E : Set Incidence} (hA : MeasurableSet A₀)
    (hE : MeasurableSet E)
    (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q)) :
    (ν.prod volume) E = ENNReal.ofReal F.q *
      ((Measure.map F.normTraj (ν.restrict A₀)).prod volume) (F.normEvent A₀ E) := by
  rw [← prod_lift_apply ν F.normTraj (ChartSystem.measurable_normTraj F) A₀ hA F.t₀ F.q hq _
    (F.measurableSet_normEvent hA hE)]
  congr 1
  ext p
  have hl : F.denormTraj (F.normTraj p.1) = p.1 := F.denormTraj_normTraj hq.ne' hD p.1
  have ht : F.t₀ + F.q * ((p.2 - F.t₀) / F.q) = p.2 := by field_simp; ring
  constructor
  · intro hp
    obtain ⟨hA', ht'⟩ := hsub p hp
    refine ⟨hA', ?_, ?_, ?_⟩
    · show F.denormTraj (F.normTraj p.1) ∈ A₀
      rw [hl]; exact hA'
    · refine ⟨div_nonneg (by linarith [ht'.1]) hq.le, ?_⟩
      rw [div_le_one hq]; linarith [ht'.2]
    · show (F.denormTraj (F.normTraj p.1), F.t₀ + F.q * ((p.2 - F.t₀) / F.q)) ∈ E
      rw [hl, ht]; exact hp
  · rintro ⟨_, _, _, h3⟩
    have h3' : (F.denormTraj (F.normTraj p.1), F.t₀ + F.q * ((p.2 - F.t₀) / F.q)) ∈ E := h3
    rw [hl, ht] at h3'
    exact h3'

end Frame
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
