import Submission.Obl.k4_raw_localized_native_systems.Window.WitnessSelection
import Submission.Obl.k4_coarsened_outer_horizon_composition.ChartMultiplicity

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

theorem chart_witness_multiplicity {p : Data} {k M D : ℕ} {κ r : ℝ}
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e')) (γ : Fin (p.W k)) (z : Point) :
    (∑ e ∈ Finset.univ.filter (fun e => W.γ e = γ),
      (W.F e).indicator (1 : Point → ENNReal) z) ≤ 2 := by
  exact k4_coarsened_outer_horizon_composition.chart_selected_multiplicity
    W.γ W.j W.A W.F hdisj
    (fun e z hz => ⟨((hW e).sel hz).2.1, ((hW e).sel hz).2.2.1⟩) γ z

/-- The actual layer geometry supplies the overlap and finiteness assumptions
for analytical heavy-witness trimming. -/
theorem chart_witness_keep_loss {p : Data} (hp : Valid p) {k M D : ℕ} {κ r : ℝ}
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ)) :
    (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
      (witnessKeep (selected p k) W.γ W.F Good γ)ᶜ) ≤
      5 * ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ := by
  apply witnessKeep_loss_le (selected p k) (fun γ => ENNReal.ofReal (p.ω k γ))
    W.γ W.F Good (fun e => (hW e).measF) hGood
  · intro e
    have hsub : W.F e ⊆ p.E k (W.γ e) := fun z hz => ((hW e).sel hz).1
    change (priorMass p k (W.γ e)).restrict (p.E k (W.γ e)) (W.F e) ≠ ⊤
    rw [Measure.restrict_eq_self _ hsub]
    exact wmass_ne_top hp (hW e)
  · exact chart_witness_multiplicity W hW hdisj

/-- The finite family of full earlier references retaining at least half their
original selected mass under the common analytical mask. -/
def heavyWitnessSet {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) : Finset (Fin W.C) := by
  classical
  exact Finset.univ.filter (activeWitness (selected p k) W.γ W.F Good)

theorem heavyWitnessSet_active {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (e : Fin W.C) :
    e ∈ heavyWitnessSet W Good ↔ activeWitness (selected p k) W.γ W.F Good e := by
  classical
  simp only [heavyWitnessSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem witnessIndex_surj {J : ℕ} (S : Finset (Fin J)) {e : Fin J} (he : e ∈ S) :
    ∃ a : Fin S.card, witnessIndex S a = e := by
  refine ⟨S.equivFin ⟨e, he⟩, ?_⟩
  simp only [witnessIndex, Equiv.symm_apply_apply]

/-- Coverage outside the common exceptional event survives the reindexing to
the heavy earlier family and lands in its entire masked witness events. -/
theorem exists_reindexed_heavy_witness {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (γ : Fin (p.W k)) {z : Point}
    (hz : z ∈ witnessKeep (selected p k) W.γ W.F Good γ)
    (hsource : ∃ e, W.γ e = γ ∧ z ∈ W.F e) :
    ∃ a : Fin (heavyWitnessSet W Good).card,
      (selectWitnesses W (heavyWitnessSet W Good)).γ a = γ ∧
        z ∈ trimmedWitnesses W (heavyWitnessSet W Good) Good a := by
  obtain ⟨e, he, heγ, hez⟩ := exists_heavy_witness Good γ hz hsource
  obtain ⟨a, ha⟩ := witnessIndex_surj (heavyWitnessSet W Good)
    ((heavyWitnessSet_active W Good e).mpr he)
  refine ⟨a, ?_, ?_⟩
  · change W.γ (witnessIndex _ a) = γ
    rwa [ha]
  · change z ∈ W.F (witnessIndex _ a) ∩ Good (W.γ (witnessIndex _ a))
    rw [ha, heγ]
    exact hez

end
end Submission.Obl.k4_raw_localized_native_systems.Window
