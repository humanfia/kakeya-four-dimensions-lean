/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformRangeLocalFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformRangeLocalFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformLocalFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformRangeFitBudgets

/-! A uniform normalized fit at every resolution in a compact power range. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity

def OriginalScalarNormalizedFitAt {d : ℝ} (Λ : Type*) [MeasurableSpace Λ]
    (K p duration : ℝ) : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    (E : Set (ℝ × Λ)) (A : Set Λ) (v Z : Λ → ℝ) (F : ℝ × Λ → ℝ) (f G : ℝ → ℝ)
    (S : ℝ → Set ℝ) (S₀ : Set ℝ),
  μ ≤ volume → MeasurableSet E → E ⊆ Icc (-1 : ℝ) 1 ×ˢ A →
  Measurable v → Measurable Z → Measurable F → f 0 = 0 →
  (∀ u t, |f u - f t| ≤ |u - t|) → (∀ v w, |G v - G w| ≤ K * |v - w|) →
  (∀ l ∈ A, |v l| ≤ K ∧ |G (v l)| ≤ K) →
  (∀ t, IntervalAD p d (K) (S t)) → IntervalAD p d (K) S₀ →
  (∀ u l, (u, l) ∈ E → F (u, l) ∈ S u ∩ Icc (-K) (K)) →
  (∀ l ∈ A, Z l ∈ S₀ ∩ Icc (-K) (K)) →
  (∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ K * p) →
  (∀ a b r : ℝ, p ≤ r →
    ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ K * r ^ (1 + d)) →
  (K)⁻¹ ≤ (μ.prod ν).real E →
  ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧ T ⊆ Icc (-1 : ℝ) 1 ∧
    (∀ u ∈ T, ∃ l, (u, l) ∈ E) ∧ ENNReal.ofReal duration ≤ volume T ∧
    |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ u ∈ T, |f u - (a + slope * u)| ≤ 13 * p

theorem uniform_original_scalar_affine_fit_between_powers_all_labels
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ k in atTop, ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      OriginalScalarNormalizedFitAt (d := d) Λ (K k) p (N k ^ (-τ)) := by
  have hb : 0 < b := ha.trans_le hab
  let σ := (1 - d) / 2
  let ε := min (1 / 2 : ℝ) (τ / (2 * b))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hdim : d ≤ 1 - σ := by dsimp [σ]; linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτgap : b * ε < τ := by
    have hle : ε ≤ τ / (2 * b) := min_le_right _ _
    have h := (le_div_iff₀ (by positivity : 0 < 2 * b)).mp hle
    nlinarith
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := original_scalar_observation_affine_fit scalar_projection_input hσ hσ1 hε
  filter_upwards [scalar_local_fit_budgets_between_powers N K hN hNt hK hsub
      ha hab hd.le hσ hε hε1 hη hp₀ hτgap] with k hk
  intro Λ _ p hlow hhigh
  have hbudget := hk p hlow hhigh
  dsimp only [OriginalScalarNormalizedFitAt]
  intro μ _ ν _ E A v Z F f G S S₀ hμ hE hEsub hv hZ hF hf0 hf hG hbound hS hS₀ hsupport hstart hmodel hjoint hmass
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hNA : 11 ≤ 51 * K k := by linarith [hK k]
  have hNB : 16 * (2 * K k + 1) + 3 ≤ 51 * K k := by linarith [hK k]
  have hn : (1 + 2 * K k) + 6 * K k + 2 * K k ^ 2 + 1 ≤ (scalarLocalFitErrorCount (K k) : ℝ) := by
    linarith [(scalarLocalFitErrorCount_bounds (hK k)).1]
  obtain ⟨T, a, slope, hTm, hTbound, hTactive, hvol, ha, hslope, hrow⟩ := hfit μ ν (d := d)
    p (K k) (K k)⁻¹ (K k) (51 * K k) (scalarLocalFitErrorCount (K k)) hμ
    hbudget.positive hbudget.scale hbudget.unit (hK k) (inv_pos.mpr hKpos) hKpos.le hdim hNA hNB
    hbudget.large hbudget.planes hbudget.graphs hbudget.support hn hbudget.collisions E A v Z F f G S S₀ hE hEsub hv hZ hF hf0 hf
    hG hbound hS hS₀ hsupport hstart hmodel hjoint hmass
  exact ⟨T, a, slope, hTm, hTbound, hTactive, (ENNReal.ofReal_le_ofReal hbudget.time).trans hvol,
    ha, hslope, hrow⟩

theorem uniform_original_scalar_affine_fit_between_powers {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ k in atTop, ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      OriginalScalarNormalizedFitAt (d := d) Λ (K k) p (N k ^ (-τ)) := by
  filter_upwards [uniform_original_scalar_affine_fit_between_powers_all_labels
    N K hN hNt hK hsub ha hab hd0 hd hτ] with k hk
  exact hk Λ

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
