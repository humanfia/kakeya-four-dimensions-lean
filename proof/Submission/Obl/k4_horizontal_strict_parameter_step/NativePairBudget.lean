/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativePairBudget.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativePairSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.ObservedPairBudget
import Submission.Obl.k4_horizontal_strict_parameter_step.OldLayerRealBudget

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Every observed true-entry domain satisfies the palette-weighted area bound
using its own whole true assignment geometry and its actual old-grid contact. -/
theorem observed_domain_area {k : ℕ} {s D : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hℓ : cfg.ℓ = cfg.κ)
    (hπ : IsProbabilityMeasure (cfg.π k)) (hD : 0 < D)
    (hDq : D ≤ cfg.timeLength k s ^ 2)
    (hχq : cfg.N k ^ (-cfg.e₀) ≤ cfg.timeLength k s ^ 2)
    {m : ℕ} {AH : Fin m → Set α} (group : Fin m → Fin 3 → ℤ)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (hgrid : ∀ i l, l ∈ AH i →
      ⌊cfg.b k l 3 / (cfg.N k ^ (-cfg.e₀))⌋ = group i 0 ∧
      ⌊cfg.b k l 0 / D⌋ = group i 1 ∧ ⌊cfg.b k l 1 / D⌋ = group i 2)
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) :
    ∀ i, (∑ g ∈ T.witnessGroups group i,
      D ^ 2 * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (g 0)) ≤
        128 * cfg.K k ^ 3 * cfg.timeLength k s ^ 3 := by
  letI := hπ
  have hKp : 0 < cfg.K k := by linarith
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold Data.timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hg : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.timeLength k s := by
    rw [hℓ]
    exact (time_length_comparison hN hKp a.time_lower a.time_upper).2
  intro i
  let t₀ : ℝ := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s
  have ht₀ : t₀ ∈ Data.I (cfg.T k s) (cfg.j k s i) := by
    refine ⟨le_rfl, ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have htunit := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht₀
  have ht₀1 : |t₀| ≤ 1 := by rw [abs_of_nonneg htunit.1]; exact htunit.2
  apply true_parameter_palette_budget (cfg.π k) (cfg.c k s i) hq hq1 hK ht₀1
    (a.coefficient_bound i 4) hg (Real.rpow_pos_of_pos hN _) hχq hD hDq
    (T.witnessGroups group i)
  intro g hg
  obtain ⟨p, hp, hpB, old, hold, hpA⟩ := T.witness_group_representative group hg
  have hgeom := a.geometry i p.1 (a.fitted_subset i hpB.1) t₀ ht₀
  have hcode := hgrid old p.1 hpA.1
  rw [hold] at hcode
  refine ⟨cfg.b k p.1, hcode.1, ?_, hcontact p hp, ?_, ?_⟩
  · ext e
    fin_cases e
    · exact hcode.2.1
    · exact hcode.2.2
  · exact hgeom.1
  · exact hgeom.2.1

/-- The actual finite matching index set has the required total reference
budget. The old layer pays the source side; original true priors pay witnesses. -/
theorem observed_reference_budget {k : ℕ} {s D ε : ℝ} (a : cfg.AssignmentLevel k s)
    (hbasic : cfg.Basic) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hℓ : cfg.ℓ = cfg.κ)
    (hD : 0 < D) (hDq : D ≤ cfg.timeLength k s ^ 2)
    (hχq : cfg.N k ^ (-cfg.e₀) ≤ cfg.timeLength k s ^ 2)
    {m : ℕ} {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ}
    {hH : Fin m → Fin 6 → ℝ} (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D (cfg.N k ^ (-s)) m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) :
    (∑ i : T.Index group (cfg.j k s), cfg.timeLength k s * D ^ 2 *
      (cfg.N k ^ (-s)) ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
        ((T.colour group (cfg.j k s) i).1 0)) ≤
      cfg.N k ^ ε * cfg.K k + 128 * cfg.K k ^ 5 := by
  obtain ⟨-, hν, hπ, hdom, -, htime, -⟩ := hbasic k
  letI := hν
  letI := hπ
  have hKp : 0 < cfg.K k := by linarith
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hmass := Submission.Obl.k4_horizontal_coefficient_count.current_total_mass_le
    (cfg.ν k) (cfg.μ k) hdom htime
  have hold := H.reference_budget_real hN ha.le hKp.le ((hσ univ).trans hmass)
  have hqJ : cfg.timeLength k s * (Fintype.card (Fin (2 ^ cfg.T k s)) : ℝ) = 1 := by
    simp only [Data.timeLength, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  apply ObservedPairs.reference_budget (T := T) (block := cfg.j k s) (group := group)
    (π := cfg.π k) hq.le ha.le hKp.le hqJ hold
    (cfg.reference_budget a hν hN hKp hℓ)
  exact cfg.observed_domain_area a hN hK hℓ hπ hD hDq hχq group T
    (fun i l hl => (H.2.2.1 i).1 l hl) hcontact

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
