import Submission.Obl.k4_horizontal_coefficient_count.HeavyOutput
import Submission.Obl.k4_horizontal_coefficient_count.Numerics
import Submission.Obl.k4_fixed_menu_density_pruning.Outer

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

/-- The analytic input at one fixed depth. -/
def HeavyCoverAt {α : Type*} [MeasurableSpace α]
    (N : ℕ → ℝ) (d e₀ u R s ε : ℝ)
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    ∃ f : PredictorFamily (b k) (N k ^ (-e₀)) (N k ^ (-u * s))
      (N k ^ (-s)) (N k ^ R) (N k ^ ε),
      f.Floors (π k) d (N k ^ (ε / 2)) (ρ k) ∧
      ρ k {p | ∃ i, p.1 ∈ f.A i}ᶜ ≤ ENNReal.ofReal (N k ^ (-c))

/-- The common buffer and coefficient exponent are chosen before the
finite family of depths or the requested output tolerance. -/
theorem layers_of_heavy_covers {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (d e₀ u R sMax : ℝ)
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (htime : ∀ k, ρ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ ρ k univ)
    (htotal : ∀ k, ρ k univ ≤ ENNReal.ofReal (K k))
    (hcover : ∀ s : ℝ, 0 < s → s < sMax → ∀ ε : ℝ, 0 < ε →
      HeavyCoverAt N d e₀ u R s ε ρ π b) :
    ∀ (m : ℕ) (sH : Fin m → ℝ), (∀ r, 0 < sH r ∧ sH r < sMax) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        ∃ ρH : Measure (α × ℝ), ρH ≤ ρ k ∧
          ENNReal.ofReal (N k ^ (-ε)) ≤ ρH univ ∧ Layers (N k) d e₀ u ε R sH ρH (π k) (b k) := by
  classical
  intro m sH hsH ε hε
  choose c hc hraw using fun r => hcover (sH r) (hsH r).1 (hsH r).2 ε hε
  have hN1 : ∀ k, 1 ≤ N k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)
  obtain ⟨c₀, hc₀, hcommon⟩ :=
    Submission.Obl.k4_fixed_menu_density_pruning.finite_common_power_tail
      N hN1 (fun r k => ENNReal.ofReal (N k ^ (-c r)))
      (fun r => ⟨c r, hc r, Filter.Eventually.of_forall (fun _ => le_rfl)⟩)
  have hbudget := eventually_output_budget hN1 hNt hK hsub hc₀ hε m
  filter_upwards [Filter.eventually_all.mpr hraw, hcommon, hbudget] with k hk hck hbk
  choose f hf herr using hk
  exact layers_from_heavy_families (by linarith [hN k]) (by linarith [hK k])
    sH (ρ k) (π k) (b k) (htime k) (hmass k) (htotal k) f hf
    (fun r => (herr r).trans (hck r)) hbk

end Submission.Obl.k4_horizontal_coefficient_count
