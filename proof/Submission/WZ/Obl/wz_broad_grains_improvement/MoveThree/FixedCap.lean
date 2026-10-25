-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FixedCap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FixedCap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0623 cb54c6d, FixedCap.lean.
Uses the accepted balanced-cluster grid API instead of copying PacketSplit grid lemmas. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondPackets
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

/-!
# Second packets inside one fixed angular cap

Pre-selection route for the large-angle branch of the second filling (x0669, 15:35Z;
x0708, 15:40Z). Before the second packet extraction keep only the rows whose direction lies
in one grid cell of a fixed mesh `s`:

* `fixed_cap_selection`: some cell carries `1 / M` of the row mass, `M = (fixedCapGrid s).card`
  depending on `s` only; the kept rows are `capRows Q' B`;
* `cap_budget_transfer`, `cap_budget_cutoff`: the budget premise of the packet extraction at
  exponent `q₀` follows from the one at `q₁ > q₀` and the mass comparison, at all small `δ`;
* `packet_angle_le_of_cap`, `capped_packet_angle`: a nonempty packet of a packet refinement
  whose rows lie in a cap of radius `r ≥ δ` has angle `θ ≤ 2^(1/β) r`, by its own broadness
  bound tested at the cap.

The constants `1/2` and `2` of `PacketRefinement` are not changed.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_balanced_cluster_cover (cell cell_mem_box norm_sub_le_of_cell_eq)

abbrev fixedCapGrid (s : ℝ) := WangZahlLot.Obl.wz_balanced_cluster_cover.box s (0 : V) 1

theorem fixedCap_cell_mem {s : ℝ} (hs : 0 < s) {u : V} (hu : ‖u‖ ≤ 1) :
    cell s u ∈ fixedCapGrid s := cell_mem_box hs (by simpa only [sub_zero] using hu)

theorem pd_le_norm_sub (u w : V) : pd u w ≤ ‖u - w‖ := min_le_left _ _

/-! ### Choosing the cap -/

/-- Pigeonhole over the grid cells of mesh `s`: the rows of one cell carry `1/M` of the row
mass, `M` the number of cells meeting the unit ball. -/
theorem fixed_cap_rows {L : ℕ} {s : ℝ} (hs : 0 < s) (ν : Fin L → V)
    (hν : ∀ j, ‖ν j‖ ≤ 1) (Q : Finset (Fin L)) (B : Fin L → Set V) :
    ∃ (u : V) (Q' : Finset (Fin L)), Q' ⊆ Q ∧ (∀ j ∈ Q', ‖ν j - u‖ ≤ 2 * s) ∧
      ∑ j ∈ Q, μ (B j) ≤ ((fixedCapGrid s).card : ENNReal) * ∑ j ∈ Q', μ (B j) := by
  classical
  have hne : (fixedCapGrid s).Nonempty :=
    ⟨_, fixedCap_cell_mem hs (u := 0) (by simp)⟩
  obtain ⟨κ, -, hmax⟩ := Finset.exists_max_image (fixedCapGrid s)
    (fun κ => ∑ j ∈ Q.filter (fun j => cell s (ν j) = κ), μ (B j)) hne
  have hfib : ∑ κ' ∈ fixedCapGrid s, ∑ j ∈ Q.filter (fun j => cell s (ν j) = κ'), μ (B j) =
      ∑ j ∈ Q, μ (B j) :=
    Finset.sum_fiberwise_of_maps_to (fun j _ => fixedCap_cell_mem hs (hν j)) _
  have hsum : ∑ j ∈ Q, μ (B j) ≤ ((fixedCapGrid s).card : ENNReal) *
      ∑ j ∈ Q.filter (fun j => cell s (ν j) = κ), μ (B j) := by
    rw [← hfib]
    calc _ ≤ ∑ _κ' ∈ fixedCapGrid s, ∑ j ∈ Q.filter (fun j => cell s (ν j) = κ), μ (B j) :=
          Finset.sum_le_sum hmax
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hQ' : (Q.filter (fun j => cell s (ν j) = κ)).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hQ'
    refine ⟨ν j₀, Q.filter (fun j => cell s (ν j) = κ), Finset.filter_subset _ _, ?_, hsum⟩
    intro j hj
    rw [Finset.mem_filter] at hj hj₀
    exact norm_sub_le_of_cell_eq hs (hj.2.trans hj₀.2.symm)
  · refine ⟨0, Q.filter (fun j => cell s (ν j) = κ), Finset.filter_subset _ _, ?_, hsum⟩
    intro j hj
    exact absurd ⟨j, hj⟩ hQ'

/-- The rows of `B` kept in `Q'`. -/
def capRows {L : ℕ} (Q' : Finset (Fin L)) (B : Fin L → Set V) (j : Fin L) : Set V :=
  if j ∈ Q' then B j else ∅

theorem capRows_subset {L : ℕ} (Q' : Finset (Fin L)) (B : Fin L → Set V) (j : Fin L) :
    capRows Q' B j ⊆ B j := by
  unfold capRows
  split_ifs
  · exact le_rfl
  · exact Set.empty_subset _

theorem capRows_measurable {L : ℕ} (Q' : Finset (Fin L)) {B : Fin L → Set V}
    (hB : ∀ j, MeasurableSet (B j)) (j : Fin L) : MeasurableSet (capRows Q' B j) := by
  unfold capRows
  split_ifs
  · exact hB j
  · exact MeasurableSet.empty

theorem capRows_of_not_mem {L : ℕ} {Q' : Finset (Fin L)} (B : Fin L → Set V) {j : Fin L}
    (hj : j ∉ Q') : capRows Q' B j = ∅ := by
  simp [capRows, hj]

theorem mem_of_capRows_nonempty {L : ℕ} {Q' : Finset (Fin L)} {B : Fin L → Set V} {j : Fin L}
    (h : (capRows Q' B j).Nonempty) : j ∈ Q' := by
  by_contra hj
  rw [capRows_of_not_mem B hj] at h
  exact Set.not_nonempty_empty h

theorem sum_capRows {L : ℕ} (Q' : Finset (Fin L)) (B : Fin L → Set V) :
    ∑ j, μ (capRows Q' B j) = ∑ j ∈ Q', μ (B j) := by
  classical
  have h : ∀ j, μ (capRows Q' B j) = if j ∈ Q' then μ (B j) else 0 := by
    intro j
    unfold capRows
    split_ifs
    · rfl
    · exact measure_empty
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_mem, Finset.univ_inter]

/-- The cap selection in the form used by the packet extraction: the kept rows `capRows Q' B`
lie in one cap of radius `2 s` and carry `1/M` of the whole row mass. -/
theorem fixed_cap_selection {L : ℕ} {s : ℝ} (hs : 0 < s) (ν : Fin L → V)
    (hν : ∀ j, ‖ν j‖ ≤ 1) (Q : Finset (Fin L)) (B : Fin L → Set V)
    (hzero : ∀ j, j ∉ Q → B j = ∅) :
    ∃ (u : V) (Q' : Finset (Fin L)), Q' ⊆ Q ∧ (∀ j ∈ Q', pd (ν j) u ≤ 2 * s) ∧
      ∑ j, μ (B j) ≤ ((fixedCapGrid s).card : ENNReal) * ∑ j, μ (capRows Q' B j) := by
  obtain ⟨u, Q', hQ', hcap, hmass⟩ := fixed_cap_rows hs ν hν Q B
  refine ⟨u, Q', hQ', fun j hj => (pd_le_norm_sub _ _).trans (hcap j hj), ?_⟩
  have hfull : ∑ j ∈ Q, μ (B j) = ∑ j, μ (B j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [hzero j hj]
    exact measure_empty
  rw [sum_capRows, ← hfull]
  exact hmass

theorem fixedCapGrid_card_pos (s : ℝ) (hs : 0 < s) : 0 < (fixedCapGrid s).card :=
  Finset.card_pos.mpr ⟨_, fixedCap_cell_mem hs (u := 0) (by simp)⟩

/-! ### The budget premise after the selection -/

/-- The high-overlap budget at `q₁` gives the one at `q₀` for any family carrying `1/M` of
the mass, once `M δ^(-q₀) ≤ δ^(-q₁)`. -/
theorem cap_budget_transfer {δ q₀ q₁ : ℝ} {M : ℕ} (hM : 0 < M)
    (hMδ : (M : ℝ) * δ ^ (-q₀) ≤ δ ^ (-q₁)) {U : Set V} {S S' : ENNReal}
    (hbudget : O (δ ^ (-q₁)) * μ U ≤ (1 / 2 : ENNReal) * S)
    (hS : S ≤ (M : ENNReal) * S') :
    O (δ ^ (-q₀)) * μ U ≤ (1 / 2 : ENNReal) * S' := by
  have hM0 : (M : ENNReal) ≠ 0 := by exact_mod_cast hM.ne'
  have hMt : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
  rw [← ENNReal.mul_le_mul_iff_right hM0 hMt]
  have hO : (M : ENNReal) * O (δ ^ (-q₀)) = O ((M : ℝ) * δ ^ (-q₀)) := by
    show (M : ENNReal) * ENNReal.ofReal (δ ^ (-q₀)) = ENNReal.ofReal ((M : ℝ) * δ ^ (-q₀))
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc (M : ENNReal) * (O (δ ^ (-q₀)) * μ U) = O ((M : ℝ) * δ ^ (-q₀)) * μ U := by
        rw [← mul_assoc, hO]
    _ ≤ O (δ ^ (-q₁)) * μ U := mul_le_mul' (ENNReal.ofReal_le_ofReal hMδ) le_rfl
    _ ≤ (1 / 2 : ENNReal) * S := hbudget
    _ ≤ (1 / 2 : ENNReal) * ((M : ENNReal) * S') := mul_le_mul' le_rfl hS
    _ = (M : ENNReal) * ((1 / 2 : ENNReal) * S') := by ring

/-- `M δ^(-q₀) ≤ δ^(-q₁)` at all small `δ` when `q₀ < q₁`. -/
theorem cap_budget_cutoff {q₀ q₁ : ℝ} (hq : q₀ < q₁) (M : ℕ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → (M : ℝ) * δ ^ (-q₀) ≤ δ ^ (-q₁) := by
  obtain ⟨d, hd, Hd⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hq) (by positivity : (0 : ℝ) < 1 / ((M : ℝ) + 1))
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have hsmall := Hd δ hδ hδd
  have hsplit : δ ^ (-q₀) = δ ^ (q₁ - q₀) * δ ^ (-q₁) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hpos : 0 < δ ^ (-q₁) := Real.rpow_pos_of_pos hδ _
  have hM1 : (M : ℝ) * δ ^ (q₁ - q₀) ≤ 1 := by
    have h1 : (M : ℝ) * δ ^ (q₁ - q₀) ≤ (M : ℝ) * (1 / ((M : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
    have h2 : (M : ℝ) * (1 / ((M : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  calc (M : ℝ) * δ ^ (-q₀) = ((M : ℝ) * δ ^ (q₁ - q₀)) * δ ^ (-q₁) := by rw [hsplit]; ring
    _ ≤ 1 * δ ^ (-q₁) := mul_le_mul_of_nonneg_right hM1 hpos.le
    _ = δ ^ (-q₁) := one_mul _

/-! ### The packet angle inside a cap -/

/-- A packet whose rows lie in a cap of radius `r ≥ δ` has angle `θ ≤ 2^(1/β) r`: its
broadness bound at the cap reads `#W ≤ 2 (r/θ)^β #W`. -/
theorem packet_angle_le_of_cap {n : ℕ} {β δ θ r : ℝ} {v : Fin n → V} {Y Z : Fin n → Set V}
    {P : V → Finset (Finset (Fin n))} {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z P a) (hβ : 0 < β) (hδ : 0 < δ) (hθ : 0 < θ)
    (hδr : δ ≤ r) (u : V) (hcap : ∀ i, (Y i).Nonempty → pd (v i) u ≤ r)
    {p : V} {W : Finset (Fin n)} (hW : W ∈ P p) : θ ≤ 2 ^ (1 / β) * r := by
  classical
  obtain ⟨hZ, -, -, hP⟩ := h
  obtain ⟨-, hunion, hWs⟩ := hP p
  obtain ⟨hne, -, -, hbr⟩ := hWs W hW
  have hin : ∀ i ∈ W, pd (v i) u ≤ r := by
    intro i hi
    have hi' : i ∈ ((P p).biUnion id : Set (Fin n)) :=
      Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨W, hW, hi⟩)
    rw [hunion] at hi'
    exact hcap i ⟨p, (hZ i).2 hi'⟩
  have hfilt : W.filter (fun i => pd (v i) u ≤ r) = W := Finset.filter_true_of_mem hin
  have hb := hbr u r hδr
  rw [hfilt] at hb
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast hne.card_pos
  have hr : 0 < r := hδ.trans_le hδr
  have hx : 0 < r / θ := div_pos hr hθ
  have h1 : 1 ≤ 2 * (r / θ) ^ β := by
    by_contra hlt
    have hlt' : 2 * (r / θ) ^ β < 1 := lt_of_not_ge hlt
    have := mul_lt_mul_of_pos_right hlt' hcard
    linarith
  have hy : (2 ^ (1 / β) * (r / θ)) ^ β = 2 * (r / θ) ^ β := by
    rw [Real.mul_rpow (by positivity) hx.le, ← Real.rpow_mul (by norm_num),
      one_div_mul_cancel hβ.ne', Real.rpow_one]
  have hy1 : 1 ≤ 2 ^ (1 / β) * (r / θ) := by
    by_contra hlt
    have hlt' : 2 ^ (1 / β) * (r / θ) < 1 := lt_of_not_ge hlt
    have := Real.rpow_lt_one (by positivity) hlt' hβ
    linarith
  calc θ = θ * 1 := (mul_one θ).symm
    _ ≤ θ * (2 ^ (1 / β) * (r / θ)) := mul_le_mul_of_nonneg_left hy1 hθ.le
    _ = 2 ^ (1 / β) * r := by field_simp

/-- A packet refinement with positive retained mass has a packet. -/
theorem exists_packet_of_mass_pos {n : ℕ} {β δ θ : ℝ} {v : Fin n → V} {Y Z : Fin n → Set V}
    {P : V → Finset (Finset (Fin n))} {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β δ θ v Y Z P a) (hpos : 0 < ∑ i, μ (Z i)) :
    ∃ p W, W ∈ P p := by
  classical
  obtain ⟨-, -, -, hP⟩ := h
  by_contra hno
  have hzero : ∀ i, Z i = ∅ := by
    intro i
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    have hi : i ∈ ((P p).biUnion id : Set (Fin n)) := by rw [(hP p).2.1]; exact hp
    obtain ⟨W, hW, -⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hi)
    exact hno ⟨p, W, hW⟩
  have hsum : ∑ i, μ (Z i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i]
    exact measure_empty
  rw [hsum] at hpos
  exact lt_irrefl _ hpos

/-- The angle of a packet refinement on cap-selected rows with positive retained mass. -/
theorem capped_packet_angle {L : ℕ} {β δ θ r : ℝ} {ν : Fin L → V} {Q' : Finset (Fin L)}
    {B : Fin L → Set V} {D : Set V} {u : V} {Z : Fin L → Set V}
    {P : V → Finset (Finset (Fin L))} {a : V → Finset (Fin L) → Fin L}
    (h : PacketRefinement β δ θ ν (fun j => capRows Q' B j ∩ D) Z P a)
    (hβ : 0 < β) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ ≤ r)
    (hcap : ∀ j ∈ Q', pd (ν j) u ≤ r) (hpos : 0 < ∑ j, μ (Z j)) :
    θ ≤ 2 ^ (1 / β) * r := by
  obtain ⟨p, W, hW⟩ := exists_packet_of_mass_pos h hpos
  refine packet_angle_le_of_cap h hβ hδ hθ hδr u (fun j hj => hcap j ?_) hW
  obtain ⟨x, hx⟩ := hj
  exact mem_of_capRows_nonempty ⟨x, hx.1⟩

/-- The mesh giving a prescribed angle bound: with `s = θmax / (4 * 2^(1/β))` the cap radius
`2 s` gives `2^(1/β) (2 s) ≤ θmax`. -/
theorem cap_mesh_angle {β θmax : ℝ} (hθmax : 0 < θmax) :
    2 ^ (1 / β) * (2 * (θmax / (4 * 2 ^ (1 / β)))) ≤ θmax := by
  have h2 : 0 < (2 : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos (by norm_num) _
  have he : 2 ^ (1 / β) * (2 * (θmax / (4 * 2 ^ (1 / β)))) = θmax / 2 := by
    field_simp; ring
  rw [he]; linarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
