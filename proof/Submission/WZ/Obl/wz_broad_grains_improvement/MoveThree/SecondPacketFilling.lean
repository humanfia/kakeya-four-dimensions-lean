-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SecondPacketFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SecondPacketFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, SecondPacketFilling.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondFillingParameters
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketPruning

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped Classical
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- Packet selection at a finer angular cutoff remains valid at a coarser
cutoff. This separates the original fine scale from the normalized body radius. -/
theorem packet_refinement_radius_mono {n : ℕ} {β δ d θ : ℝ}
    {v : Fin n → V} {Y Z : Fin n → Set V}
    {F : V → Finset (Finset (Fin n))} {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z F a) (hδd : δ ≤ d) :
    PacketRefinement β d θ v Y Z F a := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p => ?_⟩
  refine ⟨(h.2.2.2 p).1, (h.2.2.2 p).2.1, fun W hW => ?_⟩
  have hh := (h.2.2.2 p).2.2 W hW
  exact ⟨hh.1, hh.2.1, hh.2.2.1, fun u r hr => hh.2.2.2 u r (hδd.trans hr)⟩

/-- The total cost of a uniform threshold counts only nonempty rows. -/
theorem occupied_row_cost {κ : Type*} [Fintype κ] {n : ℕ}
    (Y : κ → Fin n → Set V) {m : ℝ} (hm : 0 ≤ m) :
    (∑ k, ∑ i, if (Y k i).Nonempty then O m else 0) =
      O (m * ∑ k, q n {i | (Y k i).Nonempty}) := by
  classical
  have hone (k : κ) : (∑ i, if (Y k i).Nonempty then O m else 0) =
      O (m * q n {i | (Y k i).Nonempty}) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun i => (Y k i).Nonempty)).card =
        {i | (Y k i).Nonempty}.ncard := by simp [Set.ncard_eq_toFinset_card']
    rw [hcard]
    dsimp only [O, q]
    rw [ENNReal.ofReal_mul hm, ENNReal.ofReal_natCast, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => hone k), Finset.mul_sum]
  exact (ENNReal.ofReal_sum_of_nonneg
    (fun k _ => mul_nonneg hm (Nat.cast_nonneg _))).symm

/-- The accepted packet-label count pays all row thresholds at once.
Every occupied label is filled, and half the entire packet mass survives. -/
theorem second_packet_fillings {n : ℕ} {β δ d θ L mass lam r vol : ℝ}
    {x v : Fin n → V} {Y Z : Fin n → Set V}
    {F : V → Finset (Finset (Fin n))} {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z F a)
    (hd : 0 < d) (hd1 : d ≤ 1 / 100) (hδd : δ ≤ d)
    (hθ : 0 < θ) (hdθ : d ≤ θ) (hr : d ≤ r ∧ r ≤ 1)
    (hL : 2 * d ≤ L) (hmass : 0 ≤ mass) (hlam : 0 ≤ lam)
    (hv : ∀ i, ‖v i‖ = 1) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Z i = ∅)
    (hbudget : O ((2 * 6 ^ 3 * 22 ^ 3 : ℝ) * S.card * mass) ≤
      (1 / 4 : ENNReal) * ∑ i, μ (Z i))
    (hangle : 8 * (r / θ) ^ β < 1)
    (hnum : (1000000000 * L * d ^ 5 * (1 + Real.log (1 / d))) *
      (lam * vol) ≤ mass ^ 3 * r)
    (center : (packetLabelUniverse θ x v) → V)
    (U : (packetLabelUniverse θ x v) → Set V)
    (hball : ∀ (k : packetLabelUniverse θ x v) i, packetPiece θ v Z F a k i ⊆ ball (center k) (L / 2))
    (hU : ∀ (k : packetLabelUniverse θ x v) i, packetPiece θ v Z F a k i ⊆ U k)
    (hUvol : ∀ k, μ (U k) ≤ O vol) :
    ∃ W : (packetLabelUniverse θ x v) → Fin n → Set V,
      (∀ k i, MeasurableSet (W k i) ∧ W k i ⊆ packetPiece θ v Z F a k i) ∧
      (∀ k i, W k i ⊆ U k) ∧
      (1 / 2 : ENNReal) * (∑ i, μ (Z i)) ≤ ∑ k, ∑ i, μ (W k i) ∧
      (∀ k i, (W k i).Nonempty → O mass ≤ μ (W k i)) ∧
      (∀ k p, p ∈ ⋃ i, W k i →
        q n {i | p ∈ packetPiece θ v Z F a k i} ≤ 4 * q n {i | p ∈ W k i}) ∧
      (∀ k p u s, d ≤ s →
        q n {i | p ∈ W k i ∧ pd (v i) u ≤ s} ≤
          8 * (s / θ) ^ β * q n {i | p ∈ W k i}) ∧
      ∀ k, (⋃ i, W k i).Nonempty → O lam * μ (U k) ≤ μ (⋃ i, W k i) := by
  classical
  let Q : (packetLabelUniverse θ x v) → Fin n → Set V :=
    fun k i => packetPiece θ v Z F a k i
  let cost := fun k i => if (Q k i).Nonempty then O mass else 0
  have hdpack := packet_refinement_radius_mono h hδd
  have htotal : (∑ k, ∑ i, μ (Q k i)) = ∑ i, μ (Z i) := by
    exact (Finset.sum_coe_sort _ _).trans (hdpack.piece_mass hθ hdθ hv hZT)
  have hcard : (∑ k, q n {i | (Q k i).Nonempty}) ≤
      (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * S.card := by
    exact (Finset.sum_coe_sort (packetLabelUniverse θ x v)
      (fun k => q n {i | (packetPiece θ v Z F a k i).Nonempty})).le.trans
        (WangZahlLot.Obl.wz_move_two_dense_broad_prisms.packet_piece_card_sum_support
          hdpack hθ hdθ hv hZT S hzero)
  have hcost : (∑ k, ∑ i, cost k i) ≤
      (1 / 4 : ENNReal) * ∑ k, ∑ i, μ (Q k i) := by
    rw [htotal]
    calc
      _ = O (mass * ∑ k, q n {i | (Q k i).Nonempty}) := occupied_row_cost Q hmass
      _ ≤ O (mass * ((2 * 6 ^ 3 * 22 ^ 3 : ℝ) * S.card)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcard hmass)
      _ = O ((2 * 6 ^ 3 * 22 ^ 3 : ℝ) * S.card * mass) := by congr 1; ring
      _ ≤ _ := hbudget
  obtain ⟨W, hW, hWU, hkeep, hrows, hcounts, hbroad, hdense⟩ :=
    cordoba_family_filling hd hd1 hL (fun _ => θ) (fun _ => r) (fun _ => mass)
      (fun _ => lam) (fun _ => vol) (fun _ => hθ) (fun _ => hr)
      (fun _ => hmass) (fun _ => hlam) (fun _ => x) (fun _ => v) (fun _ => hv)
      Q (fun k i => h.measurable_piece k i) (fun _ i _ hp => hZT i hp.1)
      center hball U hU hUvol
      (fun k p u s hs => WangZahlLot.Obl.wz_move_two_dense_broad_prisms.packet_piece_broad
        hdpack k p u s hs) cost (fun k i hi => by simp [cost, hi]) hcost
      (fun _ => hangle) (fun _ => hnum)
  rw [htotal] at hkeep
  exact ⟨W, hW, hWU, hkeep, hrows, hcounts, hbroad, hdense⟩

/-- The uniform packet filling with a small power loss in the containing width. -/
theorem second_packet_fillings_width_uniform {β t s u h ε vLoss L C : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3 * u + s + vLoss < ε) (hL : 0 < L) (hC : 0 < C) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1 / 100 → 2 * d ≤ L →
      δ ^ (-t) * d ≤ θ → θ ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V)
        (F : V → Finset (Finset (Fin n))) (a : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ v Y Z F a → (∀ i, ‖v i‖ = 1) →
      (∀ i, Z i ⊆ T d (x i) (v i)) →
      ∀ S : Finset (Fin n), (∀ i, i ∉ S → Z i = ∅) →
      O (δ ^ h * S.card * d ^ 2) ≤ ∑ i, μ (Z i) →
      ∀ (center : (packetLabelUniverse θ x v) → V)
        (U : (packetLabelUniverse θ x v) → Set V),
      (∀ (k : packetLabelUniverse θ x v) i,
        packetPiece θ v Z F a k i ⊆ ball (center k) (L / 2)) →
      (∀ (k : packetLabelUniverse θ x v) i, packetPiece θ v Z F a k i ⊆ U k) →
      (∀ k, μ (U k) ≤ O (C * δ ^ (-vLoss) * d * θ)) →
      ∃ W : (packetLabelUniverse θ x v) → Fin n → Set V,
        (∀ k i, MeasurableSet (W k i) ∧ W k i ⊆ packetPiece θ v Z F a k i) ∧
        (∀ k i, W k i ⊆ U k) ∧
        (1 / 2 : ENNReal) * (∑ i, μ (Z i)) ≤ ∑ k, ∑ i, μ (W k i) ∧
        (∀ k i, (W k i).Nonempty → O (δ ^ u * d ^ 2) ≤ μ (W k i)) ∧
        (∀ k p, p ∈ ⋃ i, W k i →
          q n {i | p ∈ packetPiece θ v Z F a k i} ≤ 4 * q n {i | p ∈ W k i}) ∧
        (∀ k p u' r, d ≤ r →
          q n {i | p ∈ W k i ∧ pd (v i) u' ≤ r} ≤
            8 * (r / θ) ^ β * q n {i | p ∈ W k i}) ∧
        ∀ k, (⋃ i, W k i).Nonempty → O (δ ^ ε) * μ (U k) ≤ μ (⋃ i, W k i) := by
  obtain ⟨d₁, hd₁, hd₁small, Hfill⟩ := second_filling_width_parameters hβ hs hst hgap hL hC
  obtain ⟨d₂, hd₂, Hcost⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (sub_pos.mpr hhu) (K := 1 / (4 * (2 * 6 ^ 3 * 22 ^ 3))) (by norm_num)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ d θ hδ hδ0 hδd hd1 hLd hgrow hθ1 n x v Y Z F a hpack hv hZT
    S hzero hmass center U hball hU hUvol
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hδ1 : δ ≤ 1 :=
    (hδ0.trans ((min_le_left _ _).trans hd₁small)).trans (by norm_num)
  have hdθ : d ≤ θ := by
    have hh : 1 ≤ δ ^ (-t) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    exact (show d ≤ δ ^ (-t) * d by nlinarith).trans hgrow
  obtain ⟨hr, hr1, hangle, hnum⟩ :=
    Hfill δ d θ hδ (hδ0.trans (min_le_left _ _)) hδd hgrow hθ1
  have hconst : (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * δ ^ u ≤ δ ^ h / 4 := by
    have hh := Hcost δ hδ (hδ0.trans (min_le_right _ _))
    have hp : δ ^ u = δ ^ (u - h) * δ ^ h := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [hp]
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hδ.le h)
    norm_num at hh'
    nlinarith
  have hbudget : O ((2 * 6 ^ 3 * 22 ^ 3 : ℝ) * S.card * (δ ^ u * d ^ 2)) ≤
      (1 / 4 : ENNReal) * ∑ i, μ (Z i) := by
    calc
      _ ≤ O ((1 / 4 : ℝ) * (δ ^ h * S.card * d ^ 2)) :=
        ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_right hconst
            (show 0 ≤ (S.card : ℝ) * d ^ 2 by positivity)
          nlinarith)
      _ = (1 / 4 : ENNReal) * O (δ ^ h * S.card * d ^ 2) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
          ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      _ ≤ _ := mul_le_mul' le_rfl hmass
  exact second_packet_fillings hpack hd hd1 hδd hθ hdθ ⟨hr, hr1⟩ hLd
    (by positivity) (by positivity) hv hZT S hzero hbudget hangle hnum
    center U hball hU hUvol

/-- One cutoff pays both the actual label-count cost and the Córdoba
estimate. The input density exponent is strictly smaller than the row
threshold exponent; the remaining reserve pays the cubic density loss. -/
theorem second_packet_fillings_uniform {β t s u h ε L C : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3 * u + s < ε) (hL : 0 < L) (hC : 0 < C) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1 / 100 → 2 * d ≤ L →
      δ ^ (-t) * d ≤ θ → θ ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V)
        (F : V → Finset (Finset (Fin n))) (a : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ v Y Z F a → (∀ i, ‖v i‖ = 1) →
      (∀ i, Z i ⊆ T d (x i) (v i)) →
      ∀ S : Finset (Fin n), (∀ i, i ∉ S → Z i = ∅) →
      O (δ ^ h * S.card * d ^ 2) ≤ ∑ i, μ (Z i) →
      ∀ (center : (packetLabelUniverse θ x v) → V)
        (U : (packetLabelUniverse θ x v) → Set V),
      (∀ (k : packetLabelUniverse θ x v) i,
        packetPiece θ v Z F a k i ⊆ ball (center k) (L / 2)) →
      (∀ (k : packetLabelUniverse θ x v) i, packetPiece θ v Z F a k i ⊆ U k) →
      (∀ k, μ (U k) ≤ O (C * d * θ)) →
      ∃ W : (packetLabelUniverse θ x v) → Fin n → Set V,
        (∀ k i, MeasurableSet (W k i) ∧ W k i ⊆ packetPiece θ v Z F a k i) ∧
        (∀ k i, W k i ⊆ U k) ∧
        (1 / 2 : ENNReal) * (∑ i, μ (Z i)) ≤ ∑ k, ∑ i, μ (W k i) ∧
        (∀ k i, (W k i).Nonempty → O (δ ^ u * d ^ 2) ≤ μ (W k i)) ∧
        (∀ k p, p ∈ ⋃ i, W k i →
          q n {i | p ∈ packetPiece θ v Z F a k i} ≤ 4 * q n {i | p ∈ W k i}) ∧
        (∀ k p u' r, d ≤ r →
          q n {i | p ∈ W k i ∧ pd (v i) u' ≤ r} ≤
            8 * (r / θ) ^ β * q n {i | p ∈ W k i}) ∧
        ∀ k, (⋃ i, W k i).Nonempty → O (δ ^ ε) * μ (U k) ≤ μ (⋃ i, W k i) := by
  simpa only [add_zero, neg_zero, Real.rpow_zero, mul_one] using
    second_packet_fillings_width_uniform (vLoss := 0) hβ hs hst hhu
      (by simpa only [add_zero] using hgap) hL hC


end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
