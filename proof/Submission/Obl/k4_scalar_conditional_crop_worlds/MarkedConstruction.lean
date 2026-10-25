import Submission.Obl.k4_scalar_conditional_crop_worlds.MarkedInput
import Submission.Obl.k4_scalar_conditional_crop_worlds.Lifting
import Submission.Obl.k4_scalar_conditional_crop_worlds.EventFormat

open MeasureTheory Set Filter

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- The remaining finite density-box interface, uniform in the resolution and finite table. -/
def PriorInterface (m u : ℝ) (M B A : ℕ) : Prop :=
  ∃ C D : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (N K : ℝ) (H : ℕ) (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (q : Label) (p : ℝ),
    2 ≤ N → 1 ≤ K → K + 1 ≤ N ^ B → (H : ℝ) ≤ N ^ (M : ℝ) →
    (∀ j, 0 ≤ w j) → (∑ j, w j) = 1 → (∀ j e, |b₀ j e| ≤ K) →
    p = priorMass N u (MarkedPrior (N ^ (-m)) H b₀ w) q → N ^ (-(A : ℝ) - 1) ≤ p →
    PriorData (N ^ C) D (conditionalPrior N u (MarkedPrior (N ^ (-m)) H b₀ w) q p)

/-- All source, selection, geometry and event obligations reduce to the finite prior-box
representation of a single scalar crop. -/
theorem marked_construction_of_prior (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : Subpower N K) (m u : ℝ) (M : ℕ)
    (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Coeff) (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool) (hm : 0 < m) (hu : 0 ≤ u)
    (hTables : ∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k))
    (hPrior : ∀ B A : ℕ, PriorInterface m u M B A) :
    CropConclusion N (fun k => MarkedPrior (N k ^ (-m)) (H k) (b₀ k) (w k))
      (fun k => MarkedEvent (H k) (J k) (mark k)) u := by
  obtain ⟨B, hB1, hB⟩ := exists_polynomial_envelope hN hK
  let U := ⌈u⌉₊
  have huU : u ≤ U := Nat.le_ceil u
  let A := 2 * (B + U + 3)
  let ν₀ : ℕ → Measure Line := fun k => MarkedPrior (N k ^ (-m)) (H k) (b₀ k) (w k)
  let E₀ : ℕ → Set State := fun k => MarkedEvent (H k) (J k) (mark k)
  obtain ⟨hpr, hE, hcoeff, hmass⟩ := marked_source_facts N K hN m hm M H J b₀ w mark hTables
  apply construct_from_interfaces N K ν₀ E₀ u B U hN hNt hK hu huU hpr hE hcoeff hB hmass
  · intro ψ W z p hz hp
    apply liftFacts_conditional (N ∘ ψ) (fun k => by dsimp; linarith [hN (ψ k)]) u W
      (ν₀ ∘ ψ) (E₀ ∘ ψ) _ (fun k => (hE (ψ k)).1) z p hz (fun k γ => (hp k γ).1)
    intro k
    change SFinite (ν₀ (ψ k))
    haveI : IsProbabilityMeasure (ν₀ (ψ k)) := hpr (ψ k)
    infer_instance
  · obtain ⟨C, D, hC, hD, hP⟩ := hPrior B A
    let C' := max C (M + 4)
    let D' := max D 1
    have hC' : 1 ≤ C' := hC.trans (le_max_left _ _)
    have hD' : 1 ≤ D' := le_max_right _ _
    refine ⟨C', D', hC', hD', fun k q p heq hp => ?_⟩
    obtain ⟨hJ0, hH, hJ, hJσ, hJσ2, hw, hw1, hb, hmarkmass⟩ := hTables k
    have hNp : 0 < N k := by linarith [hN k]
    have hp0 : 0 < p := (Real.rpow_pos_of_pos hNp _).trans_le hp
    have hPdata := hP (N k) (K k) (H k) (b₀ k) (w k) q p (hN k) (hK.1 k) (hB k)
      hH hw hw1 hb heq hp
    have hEdata := conditionalEvent_marked_data (hN k) u M (H k) (J k)
      (by simpa only [Real.rpow_natCast] using hH) (by simpa only [Real.rpow_natCast] using hJ)
      (by omega) (mark k) q
    have hNC : N k ^ C ≤ N k ^ C' := pow_le_pow_right₀ (by linarith [hN k]) (le_max_left _ _)
    have hNE : N k ^ (M + 4) ≤ N k ^ C' := pow_le_pow_right₀ (by linarith [hN k]) (le_max_right _ _)
    haveI : IsProbabilityMeasure (ν₀ k) := hpr k
    exact ⟨conditionalPrior_probability (N k) u (ν₀ k) q hp0 heq,
      hPdata.mono hNC (le_max_left _ _),
      conditionalPrior_ae_bound (N k) u (ν₀ k) q p (by linarith [hK.1 k]) (hcoeff k),
      hEdata.mono hNE (le_max_right _ _)⟩

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
