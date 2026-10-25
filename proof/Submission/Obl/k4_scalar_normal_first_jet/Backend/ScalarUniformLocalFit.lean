/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformLocalFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformLocalFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarObservationLocalFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformFitBudgets
import Submission.WZ.Obl.wz_ad_projection_dichotomy

/-! Uniform original-time affine fits for every normalized scalar group. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity

theorem scalar_projection_input : ProjectionDichotomy := WangZahlLot.wz_ad_projection_dichotomy

theorem uniform_original_scalar_affine_fit {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {c d τ : ℝ} (hc : 0 < c) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ k in atTop,
      let p := N k ^ (-c)
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (E : Set (ℝ × Λ)) (A : Set Λ) (v Z : Λ → ℝ) (F : ℝ × Λ → ℝ) (f G : ℝ → ℝ)
        (S : ℝ → Set ℝ) (S₀ : Set ℝ),
      μ ≤ volume → MeasurableSet E → E ⊆ Icc (-1 : ℝ) 1 ×ˢ A →
      Measurable v → Measurable Z → Measurable F → f 0 = 0 →
      (∀ u t, |f u - f t| ≤ |u - t|) → (∀ v w, |G v - G w| ≤ K k * |v - w|) →
      (∀ l ∈ A, |v l| ≤ K k ∧ |G (v l)| ≤ K k) →
      (∀ t, IntervalAD p d (K k) (S t)) → IntervalAD p d (K k) S₀ →
      (∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K k) (K k)) →
      (∀ l ∈ A, Z l ∈ S₀ ∩ Icc (-K k) (K k)) →
      (∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ K k * p) →
      (∀ a b r : ℝ, p ≤ r →
        ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ K k * r ^ (1 + d)) →
      (K k)⁻¹ ≤ (μ.prod ν).real E →
      ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc (-1 : ℝ) 1 ∧
        (∀ u ∈ T, ∃ l, (u, l) ∈ E) ∧ ENNReal.ofReal (N k ^ (-τ)) ≤ volume T ∧
        |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ u ∈ T, |f u - (a + slope * u)| ≤ 13 * p := by
  let σ := (1 - d) / 2
  let ε := min (1 / 2 : ℝ) (τ / (2 * c))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hdim : d ≤ 1 - σ := by dsimp [σ]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτgap : c * ε < τ := by
    have hle : ε ≤ τ / (2 * c) := min_le_right _ _
    have h := (le_div_iff₀ (by positivity : 0 < 2 * c)).mp hle
    nlinarith
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := original_scalar_observation_affine_fit scalar_projection_input hσ hσ1 hε
  filter_upwards [scalar_local_fit_budgets_eventually N K hN hNt hK hsub hc hd.le hσ hε1 hη hp₀ hτgap]
    with k hk
  dsimp only
  intro μ _ ν _ E A v Z F f G S S₀ hμ hE hEsub hv hZ hF hf0 hf hG hbound hS hS₀ hsupport hstart hmodel hjoint hmass
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hNA : 11 ≤ 51 * K k := by linarith [hK k]
  have hNB : 16 * (2 * K k + 1) + 3 ≤ 51 * K k := by linarith [hK k]
  have hn : (1 + 2 * K k) + 6 * K k + 2 * K k ^ 2 + 1 ≤ (scalarLocalFitErrorCount (K k) : ℝ) := by
    linarith [(scalarLocalFitErrorCount_bounds (hK k)).1]
  obtain ⟨T, a, slope, hTm, hTbound, hTactive, hvol, ha, hslope, hrow⟩ := hfit μ ν (d := d)
    (N k ^ (-c)) (K k) (K k)⁻¹ (K k) (51 * K k) (scalarLocalFitErrorCount (K k)) hμ
    hk.positive hk.scale hk.unit (hK k) (inv_pos.mpr hKpos) hKpos.le hdim hNA hNB
    hk.large hk.planes hk.graphs hk.support hn hk.collisions E A v Z F f G S S₀ hE hEsub hv hZ hF hf0 hf
    hG hbound hS hS₀ hsupport hstart hmodel hjoint hmass
  exact ⟨T, a, slope, hTm, hTbound, hTactive, (ENNReal.ofReal_le_ofReal hk.time).trans hvol,
    ha, hslope, hrow⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
