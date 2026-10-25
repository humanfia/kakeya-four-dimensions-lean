import Submission.Obl.k4_critical_affine_derivative_preparation.InputLoss
import Submission.Obl.k4_critical_affine_derivative_preparation.NativePrimitive
import Submission.Obl.k4_critical_affine_derivative_preparation.ContinuousNormalization
import Submission.Obl.k4_affine_skew_row_fit.Interfaces

/-! Recover the physical derivative primitive and the original residual mass
from the actual continuous normalized Row law. -/

namespace Submission.Obl.k4_critical_affine_derivative_preparation

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_affine_skew_row_fit

/-- The frozen Row hypothesis supplies the accepted packed interface,
with no extra assumptions on its continuous incidence data. -/
theorem uniformRowFit_of_frozen (hRow : Row) : UniformRowFit := by
  intro S a ε hS ha hε
  obtain ⟨η, hη, N₀, hN₀, h⟩ := hRow S a ε hS ha hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α inst d
  exact h N hN α d.prior d.active d.intercept d.velocity d.evaluation d.row
    d.palette d.error d.bins d.measurable_intercept d.measurable_velocity
    d.measurable_evaluation d.measurable_row d.prior_probability d.palette_probability
    d.error_lower d.error_upper d.trajectory_bound d.domination d.time_support
    d.mass_lower d.palette_cap d.joint_cap d.bins_card d.row_constraint

/-- A normalized Row event, using the convention in the frozen Row theorem. -/
def rowFitEvent {α : Type} [MeasurableSpace α] {S a η N : ℝ}
    (d : IncidenceData S a η N α) (B : Fin 2 → ℝ) (lam C : ℝ) : Set (α × ℝ) :=
  {p | |d.row p 0 - B 0 + lam * trajectoryPosition d.intercept d.velocity p 1| ≤ C * d.error ∧
    |d.row p 1 - B 1 - lam * trajectoryPosition d.intercept d.velocity p 0| ≤ C * d.error}

theorem measurableSet_rowFitEvent {α : Type} [MeasurableSpace α] {S a η N : ℝ}
    (d : IncidenceData S a η N α) (B : Fin 2 → ℝ) (lam C : ℝ) :
    MeasurableSet (rowFitEvent d B lam C) := by
  have hz : Measurable (trajectoryPosition d.intercept d.velocity) := by
    have hi := d.measurable_intercept
    have hv := d.measurable_velocity
    apply Measurable.of_eval
    intro e
    fin_cases e <;> dsimp [trajectoryPosition] <;> fun_prop
  apply MeasurableSet.inter
  · exact measurableSet_le
      (((measurable_pi_apply 0).comp d.measurable_row).sub_const (B 0) |>.add
        (((measurable_pi_apply 1).comp hz).const_mul lam)).abs measurable_const
  · exact measurableSet_le
      ((((measurable_pi_apply 1).comp d.measurable_row).sub_const (B 1)).sub
        (((measurable_pi_apply 0).comp hz).const_mul lam)).abs measurable_const

/-- The original continuous law, normalized by its original reference weight,
returns an affine derivative primitive with exactly that same reference weight. -/
theorem row_primitive_original_mass
    {α : Type} [MeasurableSpace α] {S a η N : ℝ}
    (d : IncidenceData S a η N α)
    (ρ σ : Measure (α × ℝ)) (assignment : Set α) (I : Set ℝ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (H t₀ Z₀ W K defect δ : ℝ)
    (hH : 0 < H) (hHone : H ≤ 1) (hW : 0 < W) (hK : 0 ≤ K)
    (ht₀ : |t₀| ≤ K) (hZ₀ : |Z₀| ≤ K)
    (hσ : σ ≤ ρ.restrict (assignment ×ˢ I))
    (hnorm : d.active = ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H))
    (hcoordinates : ∀ᵐ p ∂σ,
      d.intercept p.1 = (b p.1 0 + t₀ * b p.1 3 - Z₀) / H ∧
      d.velocity p.1 = b p.1 3 ∧ d.evaluation p.1 = b p.1 5)
    (hgood : ∀ᵐ p ∂σ, |b p.1 3| ≤ K ∧ |b p.1 4 + b p.1 0| ≤ defect)
    (B : Fin 2 → ℝ) (lam : ℝ)
    (hcoeff : |B 0| + |B 1| + |lam| ≤ N ^ δ)
    (hmass : ENNReal.ofReal (N ^ (-δ)) ≤ d.active (rowFitEvent d B lam (N ^ δ))) :
    ∃ L : Fin 4 → ℝ, L 0 = 0 ∧
      (∀ e : Fin 3, |L e.succ| ≤ (1 + K) * N ^ δ / H) ∧
      ENNReal.ofReal (W * N ^ (-δ)) ≤
        ρ {p | p.1 ∈ assignment ∧ p.2 ∈ I ∧
          |affineResidualSlope L (b p.1)| ≤
            N ^ η * d.error + (1 + K) * (N ^ δ * d.error) + N ^ δ * defect / H} := by
  let L := primitiveCoefficients B lam H t₀ Z₀
  let E := N ^ η * d.error + (1 + K) * (N ^ δ * d.error) + N ^ δ * defect / H
  have hL : ∀ e : Fin 3, |L e.succ| ≤ (1 + K) * N ^ δ / H :=
    primitiveCoefficients_bound B lam H t₀ Z₀ K (N ^ δ) hH hHone hK ht₀ hZ₀ hcoeff
  have hlam : |lam| ≤ N ^ δ := by linarith [abs_nonneg (B 0), abs_nonneg (B 1)]
  have hrow : ∀ᵐ p ∂σ,
      |d.row (unitTimeMap t₀ H p) 0 + d.velocity p.1 *
          d.row (unitTimeMap t₀ H p) 1 - d.evaluation p.1| ≤ N ^ η * d.error := by
    have hd := d.row_constraint.mono (fun p hp => hp.2.2)
    rw [hnorm] at hd
    exact original_continuous_normalized_ae_restore σ t₀ H W hW _ hd
  have hAE : (unitTimeMap t₀ H) ⁻¹' rowFitEvent d B lam (N ^ δ) ≤ᵐ[σ]
      {p | |affineResidualSlope L (b p.1)| ≤ E} := by
    filter_upwards [hgood, hrow, hcoordinates] with p hp hpr hc hfit
    obtain ⟨hintercept, hvelocity, hevaluation⟩ := hc
    have hf₀ :
        |d.row (unitTimeMap t₀ H p) 0 - B 0 + lam *
          ((b p.1 0 + t₀ * b p.1 3 - Z₀) / H + ((p.2 - t₀) / H) * b p.1 3)| ≤
            N ^ δ * d.error := by
      simpa only [rowFitEvent, mem_preimage, mem_ofPred_eq, trajectoryPosition,
        Matrix.cons_val_one, Matrix.cons_val_zero, hintercept, hvelocity, unitTimeMap] using hfit.1
    have hf₁ :
        |d.row (unitTimeMap t₀ H p) 1 - B 1 - lam * ((p.2 - t₀) / H)| ≤
          N ^ δ * d.error := by
      exact hfit.2
    apply normalized_row_fit_primitive_slope_bound (b p.1)
      (d.row (unitTimeMap t₀ H p)) B lam H t₀ Z₀ ((p.2 - t₀) / H)
      K (N ^ δ) (N ^ η * d.error) (N ^ δ * d.error) defect
      hH hp.1 hlam hp.2 _ hf₀ hf₁
    simpa only [hvelocity, hevaluation, abs_sub_comm, sub_sub] using hpr
  have hrestore : ENNReal.ofReal (W * N ^ (-δ)) ≤
      σ ((unitTimeMap t₀ H) ⁻¹' rowFitEvent d B lam (N ^ δ)) := by
    apply original_continuous_normalized_mass_restore σ t₀ H W (N ^ (-δ)) hW
      (rowFitEvent d B lam (N ^ δ)) (measurableSet_rowFitEvent d B lam (N ^ δ))
    simpa only [← hnorm] using hmass
  have hmeas : MeasurableSet {p : α × ℝ | |affineResidualSlope L (b p.1)| ≤ E} := by
    apply measurableSet_le _ measurable_const
    unfold affineResidualSlope
    fun_prop
  refine ⟨L, rfl, hL, ?_⟩
  calc
    _ ≤ σ {p | |affineResidualSlope L (b p.1)| ≤ E} := hrestore.trans (measure_mono_ae hAE)
    _ ≤ (ρ.restrict (assignment ×ˢ I)) {p | |affineResidualSlope L (b p.1)| ≤ E} := hσ _
    _ = ρ {p | p.1 ∈ assignment ∧ p.2 ∈ I ∧ |affineResidualSlope L (b p.1)| ≤ E} := by
      rw [Measure.restrict_apply hmeas]
      congr 1
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, mem_prod]
      tauto

/-- The recovery interface at one finite scale. All original data and
reference weights remain explicit. -/
def NativeRecoveryAt (S a η δ N : ℝ) : Prop :=
    ∀ (α : Type) [MeasurableSpace α]
      (d : IncidenceData S a η N α)
      (ρ σ : Measure (α × ℝ)) (assignment : Set α) (I : Set ℝ)
      (b : α → Fin 6 → ℝ), Measurable b →
    ∀ (H t₀ Z₀ W K defect : ℝ),
      0 < H → H ≤ 1 → 0 < W → 0 ≤ K → |t₀| ≤ K → |Z₀| ≤ K →
      σ ≤ ρ.restrict (assignment ×ˢ I) →
      d.active = ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H) →
      (∀ᵐ p ∂σ, d.intercept p.1 = (b p.1 0 + t₀ * b p.1 3 - Z₀) / H ∧
        d.velocity p.1 = b p.1 3 ∧ d.evaluation p.1 = b p.1 5) →
      (∀ᵐ p ∂σ, |b p.1 3| ≤ K ∧ |b p.1 4 + b p.1 0| ≤ defect) →
      ∃ L : Fin 4 → ℝ, L 0 = 0 ∧
        (∀ e : Fin 3, |L e.succ| ≤ (1 + K) * N ^ δ / H) ∧
        ENNReal.ofReal (W * N ^ (-δ)) ≤
          ρ {p | p.1 ∈ assignment ∧ p.2 ∈ I ∧
            |affineResidualSlope L (b p.1)| ≤
              N ^ η * d.error + (1 + K) * (N ^ δ * d.error) + N ^ δ * defect / H}

/-- Apply the frozen Row theorem with an input loss no larger than the
requested output loss, then recover the physical derivative primitive. -/
theorem native_primitive_of_Row (hRow : Row) (S a δ : ℝ)
    (hS : 0 < S) (ha : 0 < a) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → NativeRecoveryAt S a η δ N := by
  obtain ⟨η₀, hη₀, N₀, hN₀, hfit⟩ := uniformRowFit_of_frozen hRow S a δ hS ha hδ
  let η := min η₀ δ
  refine ⟨η, lt_min hη₀ hδ, min_le_right _ _, N₀, hN₀, ?_⟩
  intro N hN α inst d ρ σ assignment I b hb H t₀ Z₀ W K defect
    hH hHone hW hK ht₀ hZ₀ hσ hnorm hcoordinates hgood
  have hNone : 1 ≤ N := (by linarith : (1 : ℝ) ≤ N₀).trans hN
  obtain ⟨B, lam, hcoeff, hmass⟩ := hfit N hN α
    (enlargeIncidenceLoss d hNone (min_le_left _ _))
  exact row_primitive_original_mass d ρ σ assignment I b hb H t₀ Z₀ W K defect δ
    hH hHone hW hK ht₀ hZ₀ hσ hnorm hcoordinates hgood B lam hcoeff hmass

end

end Submission.Obl.k4_critical_affine_derivative_preparation
