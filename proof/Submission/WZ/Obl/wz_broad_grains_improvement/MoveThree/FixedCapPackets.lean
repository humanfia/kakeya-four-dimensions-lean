-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FixedCapPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FixedCapPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FixedCap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RenormScalars

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

noncomputable section

/-- A fixed direction cap can be selected before high-overlap extraction.
The constant loss is absorbed into the requested retention exponent, and
the resulting packet scale has any prescribed positive constant upper bound. -/
theorem capped_high_carrier_growing_packets {C β q₀ q₁ jump τ angleMax : ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hβ1 : β ≤ 1) (hjump : 0 < jump)
    (hmargin : 0 < q₀ - β - 3 * jump) (hτ : 0 < τ)
    (hq : q₀ < q₁) (hangle : 0 < angleMax) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ ρ : ℝ,
      0 < δ → δ ≤ d₀ → 0 < ρ →
      ∀ (n : ℕ) (v : Fin n → V) (H : Fin n → Set V) (U : Set V),
        0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (H i)) →
        MeasurableSet U → (∀ i, H i ⊆ U) →
        0 < ∑ i, μ (H i) → (∑ i, μ (H i)) ≠ ⊤ →
        O (δ ^ (-q₁)) * μ U ≤ (1 / 2 : ENNReal) * ∑ i, μ (H i) →
        (∀ p u r, ρ ≤ r → q n {i | p ∈ H i ∧ pd (v i) u ≤ r} ≤ C * (r / ρ) ^ 3) →
        ∃ (H' : Fin n → Set V) (D : Set V) (θ : ℝ) (Z : Fin n → Set V)
          (P : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
          (∀ i, MeasurableSet (H' i) ∧ H' i ⊆ H i) ∧
          MeasurableSet D ∧ δ ≤ θ ∧ θ ≤ 1 ∧ θ ≤ angleMax ∧ δ ^ (-jump) * ρ ≤ θ ∧
          PacketRefinement β δ θ v (fun i => H' i ∩ D) Z P center ∧
          O (δ ^ τ / 2) * ∑ i, μ (H i) ≤ ∑ i, μ (Z i) ∧
          ∀ p ∈ ⋃ i, H' i ∩ D, δ ^ (-q₀) < q n {i | p ∈ H' i ∩ D} := by
  classical
  let s := angleMax / (2 * 2 ^ (1 / β))
  have hs : 0 < s := by dsimp [s]; positivity
  let M := (fixedCapGrid s).card
  have hM : 0 < M := fixedCapGrid_card_pos s hs
  obtain ⟨dP, hdP, hdP1, HP⟩ := high_carrier_growing_packets
    hC hβ hβ1 hjump hmargin (by linarith : 0 < τ / 2)
  obtain ⟨dB, hdB, HB⟩ := cap_budget_cutoff hq M
  obtain ⟨dM, hdM, hdM1, HM⟩ := const_absorption
    (C := (M : ℝ)) (p := τ / 2) (q := τ) (Nat.cast_nonneg _) (by linarith)
  refine ⟨min dP (min dB (min dM (2 * s))), by positivity,
    (min_le_left _ _).trans hdP1, ?_⟩
  intro δ ρ hδ hδ0 hρ n v H U hn hv hHm hUm hsub hpos hfin hbudget hcount
  obtain ⟨hδP, hδB, hδM, hδs⟩ : δ ≤ dP ∧ δ ≤ dB ∧ δ ≤ dM ∧ δ ≤ 2 * s := by
    simpa only [le_min_iff] using hδ0
  obtain ⟨u₀, S, hSuniv, hcap, hkeep⟩ := fixed_cap_selection hs v (fun i => (hv i).le)
    Finset.univ H (by intro i hi; exact (hi (Finset.mem_univ i)).elim)
  let H' := capRows S H
  have hH'sub (i : Fin n) : H' i ⊆ H i := capRows_subset S H i
  have hpos' : 0 < ∑ i, μ (H' i) := by
    by_contra hh
    have hz : ∑ i, μ (H' i) = 0 := le_antisymm (le_of_not_gt hh) zero_le
    change (∑ i, μ (H i)) ≤ (M : ENNReal) * ∑ i, μ (H' i) at hkeep
    rw [hz, mul_zero] at hkeep
    exact (not_le_of_gt hpos) hkeep
  have hfin' : (∑ i, μ (H' i)) ≠ ⊤ := ne_top_of_le_ne_top hfin
    (Finset.sum_le_sum (fun i _ => measure_mono (hH'sub i)))
  have hbudget' : O (δ ^ (-q₀)) * μ U ≤ (1 / 2 : ENNReal) * ∑ i, μ (H' i) :=
    cap_budget_transfer hM (HB δ hδ hδB) hbudget hkeep
  have hcount' (p u : V) (r : ℝ) (hr : ρ ≤ r) :
      q n {i | p ∈ H' i ∧ pd (v i) u ≤ r} ≤ C * (r / ρ) ^ 3 := by
    apply le_trans ?_ (hcount p u r hr)
    exact Nat.cast_le.mpr (Set.ncard_le_ncard (fun i hi => ⟨hH'sub i hi.1, hi.2⟩)
      (Set.toFinite _))
  obtain ⟨D, θ, Z, P, center, hDm, hlo, hup, hgrow, hp, hm, hh⟩ :=
    HP δ ρ hδ hδP hρ n v H' U hn hv (capRows_measurable S hHm)
      hUm (fun i => (hH'sub i).trans (hsub i)) hpos' hfin' hbudget' hcount'
  have hZpos : 0 < ∑ i, μ (Z i) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ (τ / 2) / 2)).ne'
      hpos'.ne').trans_le hm
  have hθbound : θ ≤ angleMax := by
    have hh := capped_packet_angle hp hβ hδ (hδ.trans_le hlo) hδs hcap hZpos
    have he : 2 ^ (1 / β) * (2 * s) = angleMax := by
      dsimp [s]
      have hp : (2 : ℝ) ^ (1 / β) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp
    exact hh.trans_eq he
  refine ⟨H', D, θ, Z, P, center,
    fun i => ⟨capRows_measurable S hHm i, hH'sub i⟩,
    hDm, hlo, hup, hθbound, hgrow, hp, ?_, hh⟩
  calc
    _ ≤ O (δ ^ τ / 2) * ((M : ENNReal) * ∑ i, μ (H' i)) := mul_le_mul' le_rfl hkeep
    _ = O ((M : ℝ) * δ ^ τ / 2) * ∑ i, μ (H' i) := by
      dsimp only [O]
      rw [← mul_assoc, ← ENNReal.ofReal_natCast M,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ τ / 2)]
      congr 2
      ring
    _ ≤ O (δ ^ (τ / 2) / 2) * ∑ i, μ (H' i) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [HM δ hδ hδM])) le_rfl
    _ ≤ _ := hm

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
