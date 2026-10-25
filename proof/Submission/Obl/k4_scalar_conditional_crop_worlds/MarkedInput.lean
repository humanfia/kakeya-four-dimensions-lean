import Submission.Obl.k4_scalar_conditional_crop_worlds.Partition

open MeasureTheory Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- Source conditions used by the dimension-independent mass-selection construction. -/
def SourceFacts (N K : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set State) : Prop :=
  (∀ k, IsProbabilityMeasure (ν₀ k)) ∧
  (∀ k, MeasurableSet (E₀ k) ∧ E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1) ∧
  (∀ k, ∀ᵐ l ∂ν₀ k, ∀ e, |l.2 e| ≤ K k + 1) ∧
  (∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ (ν₀ k).prod volume (E₀ k))

lemma marked_source_facts (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (m : ℝ) (hm : 0 < m) (M : ℕ) (H J : ℕ → ℕ)
    (b₀ : (k : ℕ) → Fin (H k) → Coeff) (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
    (hTables : ∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) :
    SourceFacts N K (fun k => MarkedPrior (N k ^ (-m)) (H k) (b₀ k) (w k))
      (fun k => MarkedEvent (H k) (J k) (mark k)) := by
  have hσ : ∀ k, 0 < N k ^ (-m) :=
    fun k => Real.rpow_pos_of_pos (by linarith [hN k]) _
  have hσ1 : ∀ k, N k ^ (-m) ≤ 1 :=
    fun k => Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hN k]) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨hJ, hH, hJb, hJσ, hJσ2, hw, hw1, hb, hmass⟩ := hTables k
    exact k4_scalar_marked_packet_recovery.markedPrior_probability (hσ k) (b₀ k) (w k) hw hw1
  · intro k
    exact ⟨k4_scalar_marked_packet_recovery.measurableSet_markedEvent (mark k),
      k4_scalar_marked_packet_recovery.markedEvent_subset_unit (by have := (hTables k).1; omega) (mark k)⟩
  · intro k
    obtain ⟨hJ, hH, hJb, hJσ, hJσ2, hw, hw1, hb, hmass⟩ := hTables k
    exact (markedPrior_ae_bound (hσ k) (b₀ k) (w k) hb).mono
      (fun l hl e => (hl e).trans (by linarith [hσ1 k]))
  · intro k
    simpa only [MarkedLaw, Measure.restrict_apply_univ] using (hTables k).2.2.2.2.2.2.2.2

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
