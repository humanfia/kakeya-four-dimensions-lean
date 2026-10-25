import Submission.Obl.k4_critical_affine_derivative_preparation.OriginalMass
import Submission.Obl.k4_critical_affine_derivative_preparation.RowRecovery
import Submission.Obl.k4_critical_affine_derivative_preparation.LossAbsorption

namespace Submission.Obl.k4_critical_affine_derivative_preparation

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_affine_skew_row_fit

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- A Row law prepared in one original true label. The current law is a
restriction of the residual; its prior and normalizing weight are the
unchanged full true assignment and its original block length. -/
structure PreparedRowAt (cfg : Data α) (k : ℕ) (s a η : ℝ) where
  label : Fin (cfg.n k s)
  incidence : IncidenceData cfg.S a η (cfg.N k) α
  current : Measure (α × ℝ)
  time_origin : ℝ
  horizontal_origin : ℝ
  time_origin_bound : |time_origin| ≤ 4 * cfg.K k
  horizontal_origin_bound : |horizontal_origin| ≤ 4 * cfg.K k
  prior_eq : incidence.prior = (cfg.ν k (cfg.A k s label))⁻¹ •
    (cfg.ν k).restrict (cfg.A k s label)
  palette_eq : incidence.palette = cfg.π k
  reference_pos : 0 < cfg.timeLength k s * (cfg.ν k).real (cfg.A k s label)
  current_le : current ≤ (cfg.ρ k).restrict
    (cfg.B k s label ×ˢ I (cfg.T k s) (cfg.j k s label))
  normalized_eq : incidence.active =
    ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s label))⁻¹ •
      current.map (unitTimeMap time_origin (cfg.timeLength k s))
  coordinates : ∀ᵐ p ∂current,
    incidence.intercept p.1 =
      (cfg.b k p.1 0 + time_origin * cfg.b k p.1 3 - horizontal_origin) / cfg.timeLength k s ∧
    incidence.velocity p.1 = cfg.b k p.1 3 ∧ incidence.evaluation p.1 = cfg.b k p.1 5
  native_bounds : ∀ᵐ p ∂current,
    |cfg.b k p.1 3| ≤ 4 * cfg.K k ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ (4 * cfg.K k) * cfg.N k ^ (-cfg.e₀)
  error_eq : incidence.error = cfg.N k ^ (-s)
  time_upper : (cfg.timeLength k s)⁻¹ ≤ (4 * cfg.K k) * cfg.N k ^ (s / 2)

/-- The original reference mass in real units is exactly the frozen
ENNReal reference weight. -/
theorem original_reference_mass (cfg : Data α) (k : ℕ) (s θ : ℝ)
    (hν : IsProbabilityMeasure (cfg.ν k)) (i : Fin (cfg.n k s)) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) * θ) =
      ENNReal.ofReal (θ / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) := by
  let := hν
  have hH : 0 ≤ cfg.timeLength k s := by unfold timeLength; positivity
  rw [show cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) * θ =
      (θ * cfg.timeLength k s) * (cfg.ν k).real (cfg.A k s i) by ring,
    ENNReal.ofReal_mul (mul_nonneg hθ hH), measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

/-- Once the actual normalized Row inputs can be prepared at arbitrarily
small input loss, the exact original derivative-preparation conclusion follows. -/
theorem primitive_of_prepared_rows (cfg : Data α) (h : cfg.Valid) (hRow : Row)
    (s a : ℝ) (hs : 0 < s) (hsU : 1000 * s < cfg.U)
    (hse₀ : 1000 * s < cfg.e₀) (hsone : s < 1) (ha : 0 < a)
    (hprepared : ∀ η : ℝ, 0 < η → ∃ᶠ k in atTop, Nonempty (cfg.PreparedRowAt k s a η)) :
    cfg.Primitive := by
  refine ⟨s, hs, hsU, hse₀, hsone, ?_⟩
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  obtain ⟨η, hη, hηδ, N₀, hN₀, hrec⟩ :=
    native_primitive_of_Row hRow cfg.S a δ h.palette_pos ha hδ
  let Q : ℕ → ℝ := fun k => 4 * cfg.K k
  have hQ : ∀ k, 1 ≤ Q k := by intro k; dsimp [Q]; linarith [h.subpower.1 k]
  have hQsub : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k in atTop, Q k ≤ cfg.N k ^ ζ := by
    intro ζ hζ
    have hev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (fun k => (by linarith [h.scale k] : 1 ≤ cfg.N k)) h.scale_limit
      h.subpower.1 h.subpower.2 1 (show (0 : ℝ) < ζ from hζ)
      (show (0 : ℝ) ≤ 4 by norm_num)
    filter_upwards [hev] with k hk
    simpa only [Q, pow_one, Real.rpow_zero, mul_one] using hk.le
  have hbds := eventually_native_recovery_bounds h.scale h.scale_limit hQ hQsub hs
    (show 2 * s < cfg.e₀ by linarith) hδ hδε
  have hNlarge : ∀ᶠ k in atTop, N₀ ≤ cfg.N k :=
    h.scale_limit.eventually (eventually_ge_atTop N₀)
  apply ((hprepared η hη).and_eventually (hbds.and hNlarge)).mono
  rintro k ⟨⟨p⟩, hbds, hNk⟩
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hHone : cfg.timeLength k s ≤ 1 := by
    unfold timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hNkpos : 0 < cfg.N k := by linarith [h.scale k]
  have hKnonneg : 0 ≤ Q k := (hQ k).trans' (by norm_num)
  obtain ⟨L, hLzero, hL, hmass⟩ := hrec (cfg.N k) hNk α p.incidence
    (cfg.ρ k) p.current (cfg.B k s p.label) (I (cfg.T k s) (cfg.j k s p.label))
    (cfg.b k) (h.basic k).1 (cfg.timeLength k s) p.time_origin p.horizontal_origin
    (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s p.label)) (Q k)
    (Q k * cfg.N k ^ (-cfg.e₀)) hH hHone p.reference_pos hKnonneg
    p.time_origin_bound p.horizontal_origin_bound p.current_le p.normalized_eq p.coordinates p.native_bounds
  refine ⟨p.label, L, hLzero, ?_, ?_⟩
  · intro e
    calc
      |L e.succ| ≤ (1 + Q k) * cfg.N k ^ δ / cfg.timeLength k s := hL e
      _ ≤ cfg.N k ^ ε / cfg.timeLength k s := div_le_div_of_nonneg_right hbds.1 hH.le
      _ = cfg.N k ^ ε * (2 : ℝ) ^ cfg.T k s := by simp only [timeLength, div_inv_eq_mul]
  · have herr := hbds.2 η (cfg.timeLength k s) p.incidence.error
      (Q k * cfg.N k ^ (-cfg.e₀)) hηδ hH p.time_upper
      (by rw [p.error_eq]; positivity)
      (by rw [p.error_eq]; exact le_mul_of_one_le_left (by positivity) (hQ k))
      (by positivity) le_rfl
    have hηmass : cfg.N k ^ (-ε) ≤ cfg.N k ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [h.scale k]) (by linarith)
    have hρmono :
        (cfg.ρ k) {p' | p'.1 ∈ cfg.B k s p.label ∧
          p'.2 ∈ I (cfg.T k s) (cfg.j k s p.label) ∧
          |affineResidualSlope L (cfg.b k p'.1)| ≤
            cfg.N k ^ η * p.incidence.error +
            (1 + Q k) * (cfg.N k ^ δ * p.incidence.error) +
            cfg.N k ^ δ * (Q k * cfg.N k ^ (-cfg.e₀)) / cfg.timeLength k s} ≤
        (cfg.ρ k) {p' | p'.1 ∈ cfg.B k s p.label ∧
          p'.2 ∈ I (cfg.T k s) (cfg.j k s p.label) ∧
          |affineResidualSlope L (cfg.b k p'.1)| ≤ cfg.N k ^ ε * cfg.N k ^ (-s)} := by
      apply measure_mono
      intro p' hp'
      exact ⟨hp'.1, hp'.2.1, hp'.2.2.trans herr⟩
    have hν : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
    rw [← original_reference_mass cfg k s (cfg.N k ^ (-ε)) hν p.label (by positivity)]
    apply le_trans _ (hmass.trans hρmono)
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hηmass p.reference_pos.le

end Data

/-- The finite preparation task: construct actual continuous Row laws at one
fixed sufficiently small true depth and every positive input loss. -/
def CriticalRowPreparation : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid →
    ∃ s a : ℝ, 0 < s ∧ 1000 * s < cfg.U ∧ 1000 * s < cfg.e₀ ∧ s < 1 ∧ 0 < a ∧
      ∀ η : ℝ, 0 < η → ∃ᶠ k in atTop, Nonempty (cfg.PreparedRowAt k s a η)

/-- Complete assembly of the frozen conclusion from finite Row preparation. -/
theorem derivative_preparation_from_rows (hRow : Row) (hprep : CriticalRowPreparation) :
    DerivativePreparation := by
  apply derivative_preparation_of_packed
  intro α inst cfg h
  obtain ⟨s, a, hs, hsU, hse₀, hsone, ha, hprepared⟩ := hprep α cfg h
  exact cfg.primitive_of_prepared_rows h hRow s a hs hsU hse₀ hsone ha hprepared

end

end Submission.Obl.k4_critical_affine_derivative_preparation
