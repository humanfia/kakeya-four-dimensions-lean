import Submission.Obl.k4_raw_localized_native_systems.Window.ChartTrimming
import Submission.Obl.k4_raw_localized_native_systems.Pairing.ChartStrips

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

def longHeavyWitnessSet {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (lam : ℝ) : Finset (Fin W.C) := by
  classical
  exact (heavyWitnessSet W Good).filter (fun e => lam ≤ ‖longCol (W.Q e)‖)

def shortWitnessEvent {p : Data} {k : ℕ} (W : Atlas p k) (lam : ℝ)
    (γ : Fin (p.W k)) : Set Point :=
  {z | ∃ e, W.γ e = γ ∧ ‖longCol (W.Q e)‖ < lam ∧ z ∈ W.F e}

def longWitnessKeep {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (lam : ℝ) (γ : Fin (p.W k)) : Set Point :=
  witnessKeep (selected p k) W.γ W.F Good γ \ shortWitnessEvent W lam γ

theorem measurableSet_shortWitnessEvent {p : Data} {k : ℕ} (W : Atlas p k)
    (hF : ∀ e, MeasurableSet (W.F e)) (lam : ℝ) (γ : Fin (p.W k)) :
    MeasurableSet (shortWitnessEvent W lam γ) := by
  classical
  unfold shortWitnessEvent
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro e
  by_cases hw : W.γ e = γ
  · by_cases hs : ‖longCol (W.Q e)‖ < lam
    · simpa only [hw, hs, true_and, Set.setOf_mem_eq] using hF e
    · simp only [hs, false_and, and_false, Set.setOf_false, MeasurableSet.empty]
  · simp only [hw, false_and, Set.setOf_false, MeasurableSet.empty]

theorem measurableSet_longWitnessKeep {p : Data} {k : ℕ} (W : Atlas p k)
    (hF : ∀ e, MeasurableSet (W.F e)) (Good : Fin (p.W k) → Set Point)
    (hGood : ∀ γ, MeasurableSet (Good γ)) (lam : ℝ) (γ : Fin (p.W k)) :
    MeasurableSet (longWitnessKeep W Good lam γ) :=
  (measurableSet_witnessKeep (selected p k) W.γ W.F Good hF hGood γ).diff
    (measurableSet_shortWitnessEvent W hF lam γ)

theorem long_heavy_witness_major {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (lam : ℝ)
    (e : Fin (longHeavyWitnessSet W Good lam).card) :
    lam ≤ ‖longCol ((selectWitnesses W (longHeavyWitnessSet W Good lam)).Q e)‖ := by
  exact (Finset.mem_filter.mp (witnessIndex_mem (longHeavyWitnessSet W Good lam) e)).2

/-- The common original-law loss of selecting only long and heavy witnesses. -/
theorem long_witness_keep_loss {p : Data} (hp : Valid p) {k M D : ℕ} {κ r : ℝ}
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ)) (lam : ℝ) :
    (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (longWitnessKeep W Good lam γ)ᶜ) ≤
      5 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
        ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ) := by
  have hkeep := chart_witness_keep_loss hp W hW hdisj Good hGood
  calc
    _ ≤ ∑ γ, (ENNReal.ofReal (p.ω k γ) * selected p k γ
          (witnessKeep (selected p k) W.γ W.F Good γ)ᶜ +
        ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ)) := by
      apply Finset.sum_le_sum
      intro γ _
      rw [← mul_add]
      apply mul_le_mul' le_rfl
      have heq : (longWitnessKeep W Good lam γ)ᶜ =
          (witnessKeep (selected p k) W.γ W.F Good γ)ᶜ ∪ shortWitnessEvent W lam γ := by
        ext z
        simp only [longWitnessKeep, mem_compl_iff, mem_sdiff, mem_union]
        tauto
      rw [heq]
      exact measure_union_le _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hkeep le_rfl

/-- Every ancestor of a point retained by the common long-witness cutoff is
represented in the selected long-heavy family with its entire masked event. -/
theorem exists_long_heavy_witness {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (lam : ℝ) (γ : Fin (p.W k)) {z : Point}
    (hz : z ∈ longWitnessKeep W Good lam γ)
    (hsource : ∃ e, W.γ e = γ ∧ z ∈ W.F e) :
    ∃ a : Fin (longHeavyWitnessSet W Good lam).card,
      (selectWitnesses W (longHeavyWitnessSet W Good lam)).γ a = γ ∧
        z ∈ trimmedWitnesses W (longHeavyWitnessSet W Good lam) Good a := by
  classical
  obtain ⟨e, he, heγ, hez⟩ := exists_heavy_witness Good γ hz.1 hsource
  have hlong : lam ≤ ‖longCol (W.Q e)‖ := by
    apply le_of_not_gt
    intro hs
    exact hz.2 ⟨e, heγ, hs, hez.1⟩
  have heS : e ∈ longHeavyWitnessSet W Good lam :=
    Finset.mem_filter.mpr ⟨(heavyWitnessSet_active W Good e).mpr he, hlong⟩
  obtain ⟨a, ha⟩ := witnessIndex_surj (longHeavyWitnessSet W Good lam) heS
  refine ⟨a, ?_, ?_⟩
  · change W.γ (witnessIndex _ a) = γ
    rwa [ha]
  · change z ∈ W.F (witnessIndex _ a) ∩ Good (W.γ (witnessIndex _ a))
    rw [ha, heγ]
    exact hez

/-- Every retained full masked law keeps the actual original floor at enlarged
slack, including after the major-axis selection. -/
theorem long_heavy_witness_floor {p : Data} (hp : Valid p) {k M D : ℕ}
    {W : Atlas p k} {κ κ' r : ℝ} (hκ : 0 < κ) (hdouble : 2 * κ ≤ κ')
    (hW : ∀ e, WChart p k W M D κ r e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ wmass W e)
    (Good : Fin (p.W k) → Set Point) (lam : ℝ)
    (e : Fin (longHeavyWitnessSet W Good lam).card) :
    ENNReal.ofReal (p.N k ^ (-p.f r) *
      |((selectWitnesses W (longHeavyWitnessSet W Good lam)).Q e).det| /
      ((2 : ℝ) ^ (selectWitnesses W (longHeavyWitnessSet W Good lam)).T * κ')) ≤
        rawMass (selectWitnesses W (longHeavyWitnessSet W Good lam))
          (trimmedWitnesses W (longHeavyWitnessSet W Good lam) Good) e := by
  apply trimmed_witness_floor hp hκ hdouble hW hfloor Good _ _ e
  intro b hb
  exact (heavyWitnessSet_active W Good b).mp (Finset.mem_filter.mp hb).1

/-- Original coverage exceeding the common density and short-major tails
provides a default label in the long-heavy earlier family. -/
theorem long_heavy_witness_nonempty {p : Data} (hp : Valid p) {k M D : ℕ} {κ r : ℝ}
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ)) (lam : ℝ)
    (hsmall : 10 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
      2 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ)) <
        ∑ e, ENNReal.ofReal (p.ω k (W.γ e)) * wmass W e) :
    Nonempty (Fin (longHeavyWitnessSet W Good lam).card) := by
  classical
  by_contra hnone
  let Keep := longWitnessKeep W Good lam
  have hdiff (e : Fin W.C) : W.F e \ Keep (W.γ e) = W.F e := by
    apply Subset.antisymm sdiff_subset
    intro z hz
    refine ⟨hz, ?_⟩
    intro hkeep
    obtain ⟨a, _, _⟩ := exists_long_heavy_witness W Good lam (W.γ e) hkeep ⟨e, rfl, hz⟩
    exact hnone ⟨a⟩
  have heq (e : Fin W.C) : selected p k (W.γ e) (W.F e) = wmass W e := by
    rw [selected, Measure.restrict_eq_self _ (fun z hz => ((hW e).sel hz).1)]
    rfl
  have hdrop := k4_true_forest_own_depth_preparation.weighted_common_cut_loss
    (selected p k) (fun γ => ENNReal.ofReal (p.ω k γ)) W.γ W.F Keep
    (fun e => (hW e).measF)
    (measurableSet_longWitnessKeep W (fun e => (hW e).measF) Good hGood lam)
    (chart_witness_multiplicity W hW hdisj)
  simp only [hdiff, heq] at hdrop
  have hsource := hdrop.trans (mul_le_mul' le_rfl
    (long_witness_keep_loss hp W hW hdisj Good hGood lam))
  have hbound : (∑ e, ENNReal.ofReal (p.ω k (W.γ e)) * wmass W e) ≤
      10 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
        2 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ)) := by
    convert hsource using 1 <;> ring
  exact (not_lt_of_ge hbound) hsmall

end
end Submission.Obl.k4_raw_localized_native_systems.Window
