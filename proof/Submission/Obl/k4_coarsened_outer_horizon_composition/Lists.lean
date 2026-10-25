import Submission.Obl.k4_coarsened_outer_horizon_composition.CrossingCutFormat
import Submission.Obl.k4_coarsened_outer_horizon_composition.Pruning

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set MeasureTheory

theorem crossCount_eq_envelopeList {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) (w : Fin W) (o : Obs) :
    crossCount (Finset.univ.filter (fun i => γ i = w)) S o =
      ((envelopeList γ S w o).card : ENNReal) := by
  classical
  rw [crossCount_eq_card]
  simp [envelopeList, Finset.filter_filter]

theorem envelope_card_le_iff {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) (w : Fin W) (o : Obs) {θ : ℝ} (hθ : 0 ≤ θ) :
    ((envelopeList γ S w o).card : ℝ) ≤ θ ↔
      crossCount (Finset.univ.filter (fun i => γ i = w)) S o ≤ ENNReal.ofReal θ := by
  rw [crossCount_eq_envelopeList, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff hθ]

theorem measurableSet_envelope_card_le {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) (hS : ∀ i, MeasurableSet (S i)) (w : Fin W)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    MeasurableSet {o : Obs | ((envelopeList γ S w o).card : ℝ) ≤ θ} := by
  simp_rw [envelope_card_le_iff γ S w _ hθ]
  exact measurableSet_le (measurable_crossCount _ S hS) measurable_const

/-- Erase an entire overfull list; all retained incidences see an unchanged list. -/
noncomputable def shortEnvelopeList {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) (θ : ℝ) (w : Fin W) (o : Obs) : Finset (Fin C) := by
  classical
  exact if ((envelopeList γ S w o).card : ℝ) ≤ θ then envelopeList γ S w o else ∅

theorem shortEnvelopeList_card {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) {θ : ℝ} (hθ : 0 ≤ θ) (w : Fin W) (o : Obs) :
    ((shortEnvelopeList γ S θ w o).card : ℝ) ≤ θ := by
  classical
  unfold shortEnvelopeList
  split_ifs with h
  · exact h
  · simpa using hθ

theorem mem_shortEnvelopeList {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) {θ : ℝ} {b : Fin C} {o : Obs}
    (hc : ((envelopeList γ S (γ b) o).card : ℝ) ≤ θ) (hb : o ∈ S b) :
    b ∈ shortEnvelopeList γ S θ (γ b) o := by
  classical
  rw [shortEnvelopeList, if_pos hc]
  simp [envelopeList, hb]

/-- The native-coordinate cutoff used to keep the selected chart incidences. -/
noncomputable def envelopeGood {C W : ℕ} (γ : Fin C → Fin W) (S : Fin C → Set Obs)
    (θ : ℝ) (bins : Finset ℤ) (w : Fin W) (B a : ℝ) : Set Inc :=
  {p | (obs B a p).2 ∈ bins ∧ ((envelopeList γ S w (obs B a p)).card : ℝ) ≤ θ}

theorem measurableSet_envelopeGood {C W : ℕ} (γ : Fin C → Fin W)
    (S : Fin C → Set Obs) (hS : ∀ i, MeasurableSet (S i))
    {θ : ℝ} (hθ : 0 ≤ θ) (bins : Finset ℤ) (w : Fin W) (B a : ℝ) :
    MeasurableSet (envelopeGood γ S θ bins w B a) := by
  exact ((Finset.measurableSet bins).preimage (measurable_snd.comp (measurable_obs B a))).inter
    ((measurableSet_envelope_card_le γ S hS w hθ).preimage (measurable_obs B a))

end Submission.Obl.k4_coarsened_outer_horizon_composition
