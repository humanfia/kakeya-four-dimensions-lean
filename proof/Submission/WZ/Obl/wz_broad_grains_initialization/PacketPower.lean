-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PacketPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.MeasurablePackets
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketCount
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.PowerBudget

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_measurable_angular_selection (pd)

/-- The factor two and the number of angular scales fit into any positive
power loss, independently of the broadness exponent. -/
theorem angular_packet_power_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      2 ≤ δ ^ (-(ε / 2)) ∧
      ∀ K : ℕ, δ ≤ (1 / 2 : ℝ) ^ K → δ ^ ε ≤ 1 / (2 * ((K : ℝ) + 1)) := by
  obtain ⟨d₁, hd₁, _, hconst⟩ :=
    wz_ad_dichotomy_from_separated.exists_power_bound 2 (half_pos hε)
  refine ⟨min (1 / 100) (min d₁ (Real.exp (-(4 / (ε / 2) ^ 2)))),
    by positivity, min_le_left _ _, ?_⟩
  intro δ hδ hδd
  have hdsmall := (hδd.trans (min_le_right _ _))
  have hc := hconst δ hδ (hdsmall.trans (min_le_left _ _))
  refine ⟨hc, ?_⟩
  intro K hK
  have hl := wz_measurable_angular_selection.log_count_bound (half_pos hε) hδ
    (hdsmall.trans (min_le_right _ _)) hK
  have hc' : 2 * δ ^ (ε / 2) ≤ 1 := by
    calc
      _ ≤ δ ^ (-(ε / 2)) * δ ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hδ.le _)
      _ = 1 := by rw [← Real.rpow_add hδ]; simp
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((K : ℝ) + 1))).mpr
  calc
    δ ^ ε * (2 * ((K : ℝ) + 1)) =
        (2 * δ ^ (ε / 2)) * (((K : ℝ) + 1) * δ ^ (ε / 2)) := by
      have he : δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ 1 * 1 := mul_le_mul hc' hl (by positivity) (by norm_num)
    _ = 1 := one_mul _

/-- Arbitrarily small loss in measurable angular packet selection. -/
theorem measurable_angular_packets_power {β ε : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
    ∀ (n : ℕ) (v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      ∃ (θ : ℝ) (Z : Fin n → Set Space)
        (P : Space → Finset (Finset (Fin n))) (a : Space → Finset (Fin n) → Fin n),
        δ ≤ θ ∧ θ ≤ 1 ∧ PacketRefinement β δ θ v Y Z P a ∧
        ENNReal.ofReal (δ ^ ε) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
  obtain ⟨d, hd, hd100, hbudget⟩ := angular_packet_power_budget hε
  refine ⟨d, hd, hd100, ?_⟩
  intro δ hδ hδd n v Y hn hv hY
  have hδ1 : δ ≤ 1 := (hδd.trans hd100).trans (by norm_num)
  obtain ⟨K, hK1, hK2⟩ := wz_regular_transverse_affine_cells.exists_dyadic_bottom hδ hδ1
  obtain ⟨k, Z, P, a, hdata, hmass⟩ := measurable_angular_packets hn v hv Y hY hβ hβ1 hδ hK2
  refine ⟨(1 / 2 : ℝ) ^ (k : ℕ), Z, P, a, ?_, ?_, hdata, ?_⟩
  · exact hK1.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.lt_succ_iff.mp k.isLt))
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · apply le_trans _ hmass
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal ((hbudget δ hδ hδd).2 K hK1)) le_rfl

/-- The number of simultaneously occupied packets is a power of the selected
angular scale. -/
theorem PacketRefinement.card_bound {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (p : Space) : (P p).card ≤ (2 * θ ^ (-β) : ℝ) := by
  classical
  let S := {i : Fin n | p ∈ Y i}.toFinset
  have hp := h.2.2.2 p
  apply angular_packet_count hθ S (P p) (fun W hW => (hp.2.2 W hW).1) _ hp.1
  · intro W hW
    simpa only [S, Set.ncard_eq_toFinset_card'] using (hp.2.2 W hW).2.2.1
  · intro W hW i hi
    have hiU : i ∈ (P p).biUnion id := Finset.mem_biUnion.mpr ⟨W, hW, hi⟩
    have hiZ : p ∈ Z i := by
      change i ∈ {i | p ∈ Z i}
      rw [← hp.2.1]
      exact hiU
    exact Set.mem_toFinset.mpr ((h.1 i).2 hiZ)

/-- Summing the disjoint packet estimates gives broadness of the whole
retained incidence multiset, normalized at the selected angular scale. -/
theorem PacketRefinement.broad_union {n : ℕ} {β δ θ : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (p u : Space) (r : ℝ) (hr : δ ≤ r) :
    ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      2 * (r / θ) ^ β * ({i | p ∈ Z i}.ncard : ℝ) := by
  classical
  have hp := h.2.2.2 p
  have he : {i | p ∈ Z i ∧ pd (v i) u ≤ r} =
      (((P p).biUnion id).filter (fun i => pd (v i) u ≤ r) : Set (Fin n)) := by
    ext i
    change (i ∈ {i | p ∈ Z i} ∧ pd (v i) u ≤ r) ↔ _
    rw [← hp.2.1]
    simp
  rw [he, ← hp.2.1, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact angular_packet_union v (P p) hp.1 (fun W hW => (hp.2.2 W hW).2.2.2) u r hr

end WangZahlLot.Obl.wz_broad_grains_initialization
