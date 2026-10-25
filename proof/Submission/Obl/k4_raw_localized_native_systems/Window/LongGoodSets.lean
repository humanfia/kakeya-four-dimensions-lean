import Submission.Obl.k4_raw_localized_native_systems.Window.CurrentCuts
import Submission.Obl.k4_raw_localized_native_systems.Window.GoodSets
import Submission.Obl.k4_raw_localized_native_systems.Packing.MaskedWindow

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing Packing

noncomputable section

/-- Select long-heavy earlier references, cut current incidences analytically,
and apply angular charging on that selected family. The final good sets remain
subsets of the original formatted current events and use the full masked laws. -/
theorem exists_long_good_sets {p : Data} (hp : Valid p) {k M D : ℕ}
    {κ r u τ θ lam ρ σ : ℝ} (W : Atlas p k) (hκ : 0 < κ)
    (hW : ∀ e, WChart p k W M D κ r e) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ))
    (hGoodAng : ∀ γ z, z ∈ Good γ → AngGood p k γ u τ z)
    (lst₁ : Fin (p.W k) → Observation →
      Finset (Fin (longHeavyWitnessSet W Good lam).card)) (κ₁ : ℕ)
    (hcard₁ : ∀ γ o, (lst₁ γ o).card ≤ κ₁)
    (hmeas₁ : ∀ γ e, MeasurableSet {o | e ∈ lst₁ γ o})
    (hknown₁ : ∀ e z, z ∈ (selectWitnesses W (longHeavyWitnessSet W Good lam)).F e →
      e ∈ lst₁ ((selectWitnesses W (longHeavyWitnessSet W Good lam)).γ e)
        (obs (p.B k ((selectWitnesses W (longHeavyWitnessSet W Good lam)).γ e))
          (δ (p.N k) r) z))
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (hFC : ∀ a, MeasurableSet (FC a)) (hFCE : ∀ a, FC a ⊆ p.E k (γC a))
    (hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (lstC : Fin (p.W k) → Observation → Finset (Fin C)) (κC : ℕ)
    (hcardC : ∀ γ o, (lstC γ o).card ≤ κC)
    (hmeasC : ∀ γ a, MeasurableSet {o | a ∈ lstC γ o})
    (hknownC : ∀ a z, z ∈ FC a →
      a ∈ lstC (γC a) (obs (p.B k (γC a)) (δ (p.N k) p.L) z))
    (nC : Fin C → Plane) (spC : Fin C → ℝ) (hnC : ∀ a, ‖nC a‖ = 1)
    (hspC : ∀ a z, z ∈ FC a → |inner ℝ (nC a) (v z.1) - spC a| ≤ ρ)
    (hanc : ∀ a z, z ∈ FC a → ∃ e, W.γ e = γC a ∧ z ∈ W.F e)
    (hu : 0 < u) (huη : u ≤ p.η * p.L) (hθ : 0 < θ)
    (hσ : ∀ e, minorWidth ((selectWitnesses W (longHeavyWitnessSet W Good lam)).Q e) *
      (2 * κ * (2 : ℝ) ^ W.T) ≤ σ)
    (hpin : 4 * (ρ + σ) / θ ≤ δ (p.N k) u)
    (hshort : 4 * κ * (2 : ℝ) ^ W.T * lam ≤ δ (p.N k) u) :
    ∃ G : Fin C → Set Point, (∀ a, MeasurableSet (G a)) ∧ (∀ a, G a ⊆ FC a) ∧
      (∀ a, G a ⊆ rawSupportSet (selectWitnesses W (longHeavyWitnessSet W Good lam))
        (maskedWitnessEvents (selectWitnesses W (longHeavyWitnessSet W Good lam)) Good)
        (angleCompat (selectWitnesses W (longHeavyWitnessSet W Good lam)) γC nC θ lam) FC a) ∧
      (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (FC a \ G a)) ≤
        6 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
          (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ)) +
            ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
              ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) := by
  let V := selectWitnesses W (longHeavyWitnessSet W Good lam)
  let Keep := longWitnessKeep W Good lam
  let F' := fun a => FC a ∩ Keep (γC a)
  let Compat := angleCompat V γC nC θ lam
  let G := rawSupportSet V V.F Compat F'
  have hV : ∀ e, WChart p k V M D κ r e :=
    fun e => selected_witness_chart hp hκ le_rfl hW (longHeavyWitnessSet W Good lam) e
  have hKeep : ∀ γ, MeasurableSet (Keep γ) :=
    measurableSet_longWitnessKeep W (fun e => (hW e).measF) Good hGood lam
  have hF' : ∀ a, MeasurableSet (F' a) := fun a => (hFC a).inter (hKeep _)
  have hG : ∀ a, MeasurableSet (G a) := fun a =>
    measurableSet_certSupport (rawAtlas V V.F) Compat (fun e => (hV e).measF) hF' a
  have hGF : ∀ a, G a ⊆ FC a := fun _ _ hz => hz.1.1
  have hsupport : ∀ a, G a ⊆ rawSupportSet V (maskedWitnessEvents V Good) Compat FC a := by
    intro a z hz
    obtain ⟨e, he, hze⟩ := mem_iUnion.mp hz.2
    refine ⟨hz.1.1, mem_iUnion.mpr ⟨e, he, hze, ?_⟩⟩
    rw [he.1]
    exact hz.1.2.1.1
  have hanc' : ∀ a z, z ∈ F' a → ∃ e, V.γ e = γC a ∧ z ∈ V.F e := by
    intro a z hz
    obtain ⟨e, heγ, hez⟩ := exists_long_heavy_witness W Good lam (γC a) hz.2 (hanc a z hz.1)
    exact ⟨e, heγ, hez.1⟩
  have hcut := current_common_cut_loss γC FC hFC hFCE hFCdisj Keep
  have hcut' : (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (FC a \ F' a)) ≤
      5 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
        ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ) := by
    apply le_trans _ (long_witness_keep_loss hp W hW hdisj Good hGood lam)
    convert hcut using 1
    congr 1
    funext a
    congr 2
    ext z
    simp only [F', mem_sdiff, mem_inter_iff]
    tauto
  have hangleBad : (∑ γ, ENNReal.ofReal (p.ω k γ) *
      selected p k γ {z | ¬ AngGood p k γ u τ z}) ≤
      ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ := by
    apply Finset.sum_le_sum
    intro γ _
    apply mul_le_mul' le_rfl
    exact measure_mono (fun z hz hzg => hz (hGoodAng γ z hzg))
  have homit := good_set_omission (τ := τ) hp V hV hr hrL lst₁ κ₁ hcard₁ hmeas₁ hknown₁
    V.F (fun e => (hV e).measF) (fun _ => Subset.rfl) γC F' hF'
    (fun a => inter_subset_left.trans (hFCE a))
    (fun a a' hne hγ => (hFCdisj a a' hne hγ).mono inter_subset_left inter_subset_left)
    lstC κC hcardC hmeasC (fun a z hz => hknownC a z hz.1) nC spC hnC
    (fun a z hz => hspC a z hz.1) hanc' hu huη hθ hσ hpin hshort
  simp only [sdiff_self, iUnion_empty, measure_empty, mul_zero, Finset.sum_const_zero,
    zero_add] at homit
  refine ⟨G, hG, hGF, hsupport, ?_⟩
  calc
    _ ≤ (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (FC a \ F' a)) +
        ∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (F' a \ G a) :=
      current_omission_split γC FC F' G
    _ ≤ (5 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
          ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (shortWitnessEvent W lam γ)) +
        ((∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
          ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
            ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal)) :=
      add_le_add hcut' (homit.trans (add_le_add hangleBad le_rfl))
    _ = _ := by ring

end
end Submission.Obl.k4_raw_localized_native_systems.Window
