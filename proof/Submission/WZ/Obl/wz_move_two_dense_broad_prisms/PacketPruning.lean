-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PacketPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketCore
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume

/-! Selecting one uniformly massful labelled angular packet. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal
open wz_broad_grains_initialization (PacketRefinement PacketLabel packetPiece packetLabelUniverse)
open wz_measurable_angular_selection (pd)

/-- The label incidence bound charges only occupied original tubes. -/
theorem packet_piece_card_sum_support {n : ℕ} {β d θ : ℝ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β d θ v Y Z F a) (hθ : 0 < θ) (hdθ : d ≤ θ)
    (hv : ∀ i, ‖v i‖ = 1) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Z i = ∅) :
    (∑ ℓ ∈ packetLabelUniverse θ x v,
      q n {i | (packetPiece θ v Z F a ℓ i).Nonempty}) ≤
        (2*6^3*22^3 : ℝ)*S.card := by
  classical
  let Λ := packetLabelUniverse θ x v
  let A : PacketLabel → Finset (Fin n) := fun ℓ =>
    Finset.univ.filter (fun i => (packetPiece θ v Z F a ℓ i).Nonempty)
  have hflip : ∑ ℓ ∈ Λ, (A ℓ).card = ∑ i : Fin n,
      (Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty)).card := by
    simpa only [A, Finset.bipartiteAbove, Finset.bipartiteBelow] using
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun ℓ i => (packetPiece θ v Z F a ℓ i).Nonempty)
        (s := Λ) (t := (Finset.univ : Finset (Fin n)))
  have hb (i : Fin n) :
      ((Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty)).card : ℝ) ≤
        if i ∈ S then 2*6^3*22^3 else 0 := by
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      have hsub : Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty) ⊆
          wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i) := by
        intro ℓ hℓ
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hℓ).2
        exact h.piece_label hθ hdθ hv hZT hp
      have hh : ((Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty)).card : ℝ) ≤
          (wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i)).card := by
        exact_mod_cast Finset.card_le_card hsub
      refine hh.trans ?_
      convert wz_balanced_cluster_cover.card_labelBox_le hθ (by norm_num : (0:ℝ) ≤ 2)
        (x i) (v i) using 1 <;> norm_num
    · rw [if_neg hi]
      have he : Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ℓ hℓ
        obtain ⟨p, hp, _⟩ := (Finset.mem_filter.mp hℓ).2
        simpa only [hzero i hi, mem_empty_iff_false] using hp
      simp [he]
  calc
    _ = ∑ ℓ ∈ Λ, ((A ℓ).card : ℝ) := by
      simp [A, Λ, q, wz_move_two_long_grains_gain.q, Set.ncard_eq_toFinset_card']
    _ = ∑ i : Fin n,
        ((Λ.filter (fun ℓ => (packetPiece θ v Z F a ℓ i).Nonempty)).card : ℝ) := by
      exact_mod_cast hflip
    _ ≤ ∑ i : Fin n, if i ∈ S then (2*6^3*22^3 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by rw [← Finset.sum_filter]; simp [mul_comm]


/-- A positive-mass angular refinement has a labelled packet with uniformly
massful pieces and pointwise broadness. Only its occupied original support is
charged for the row pruning. -/
theorem exists_massful_broad_packet {n : ℕ} {β d θ mass : ℝ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β d θ v Y Z F a)
    (hd : 0 < d) (hθ : 0 < θ) (hdθ : d ≤ θ) (hmass : 0 ≤ mass)
    (hv : ∀ i, ‖v i‖ = 1) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Z i = ∅)
    (hpos : 0 < ∑ i, volume (Z i))
    (hbudget : O ((2*6^3*22^3 : ℝ)*S.card*mass) ≤
      (1/4 : ENNReal) * ∑ i, volume (Z i)) :
    ∃ R : Fin n → Set V, ∃ i₀ : Fin n,
      (∀ i, MeasurableSet (R i) ∧ R i ⊆ Z i) ∧ (R i₀).Nonempty ∧
      (∀ i, (R i).Nonempty → O mass ≤ volume (R i)) ∧
      (∀ i, (R i).Nonempty → pd (v i) (v i₀) ≤ 8*θ) ∧
      ∀ p u r, d ≤ r → q n {i | p ∈ R i ∧ pd (v i) u ≤ r} ≤
        8*(r/θ)^β*q n {i | p ∈ R i} := by
  classical
  let Λ := packetLabelUniverse θ x v
  let U : Λ → Fin n → Set V := fun ℓ i => packetPiece θ v Z F a ℓ i
  let cost : Λ → Fin n → ENNReal := fun ℓ i => if (U ℓ i).Nonempty then O mass else 0
  have hUm (ℓ : Λ) (i : Fin n) : MeasurableSet (U ℓ i) := h.measurable_piece ℓ i
  have hUZ (ℓ : Λ) (i : Fin n) : U ℓ i ⊆ Z i := fun _ hp => hp.1
  have hUfin (ℓ : Λ) (i : Fin n) : volume (U ℓ i) ≠ ∞ :=
    measure_ne_top_of_subset ((hUZ ℓ i).trans (hZT i))
      (wz_flat_cluster_slab_filling.tube_volume_ne_top d (x i) (v i))
  have hUtotal : (∑ ℓ : Λ, ∑ i, volume (U ℓ i)) = ∑ i, volume (Z i) := by
    exact (Finset.sum_coe_sort Λ (fun ℓ => ∑ i, volume (packetPiece θ v Z F a ℓ i))).trans
      (h.piece_mass hθ hdθ hv hZT)
  have hcount : (∑ ℓ : Λ, q n {i | (U ℓ i).Nonempty}) ≤
      (2*6^3*22^3 : ℝ)*S.card := by
    calc
      _ = ∑ ℓ ∈ Λ, q n {i | (packetPiece θ v Z F a ℓ i).Nonempty} :=
        Finset.sum_coe_sort Λ (fun ℓ => q n {i | (packetPiece θ v Z F a ℓ i).Nonempty})
      _ ≤ _ := packet_piece_card_sum_support h hθ hdθ hv hZT S hzero
  have hrowcost (ℓ : Λ) : (∑ i, cost ℓ i) = O (q n {i | (U ℓ i).Nonempty}*mass) := by
    change (∑ i, if (U ℓ i).Nonempty then O mass else 0) = _
    rw [← Finset.sum_filter]
    have hc : (Finset.univ.filter (fun i => (U ℓ i).Nonempty)).card =
        {i | (U ℓ i).Nonempty}.ncard := by simp [Set.ncard_eq_toFinset_card']
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    change ({i | (U ℓ i).Nonempty}.ncard : ENNReal)*O mass =
      O (({i | (U ℓ i).Nonempty}.ncard : ℝ)*mass)
    change ({i | (U ℓ i).Nonempty}.ncard : ENNReal)*ENNReal.ofReal mass =
      ENNReal.ofReal (({i | (U ℓ i).Nonempty}.ncard : ℝ)*mass)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp
  have hcost : (∑ ℓ : Λ, ∑ i, cost ℓ i) ≤
      (1/4 : ENNReal) * ∑ ℓ : Λ, ∑ i, volume (U ℓ i) := by
    rw [hUtotal]
    refine le_trans ?_ hbudget
    calc
      _ = O (∑ ℓ : Λ, q n {i | (U ℓ i).Nonempty}*mass) := by
        simp_rw [hrowcost]
        exact (ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hcount hmass)
  obtain ⟨R, hR, hretain, hmassR, hBrR⟩ := broad_packet_core hd hθ v U hUm hUfin
    (fun ℓ p u r hr => packet_piece_broad h ℓ p u r hr) cost hcost
  have hRpos : 0 < ∑ ℓ : Λ, ∑ i, volume (R ℓ i) := by
    apply lt_of_lt_of_le _ hretain
    rw [hUtotal]
    exact bot_lt_iff_ne_bot.mpr (mul_ne_zero (by norm_num) hpos.ne')
  obtain ⟨ℓ, _, hℓ⟩ := Finset.sum_pos_iff.mp hRpos
  obtain ⟨i₀, _, hi₀⟩ := Finset.sum_pos_iff.mp hℓ
  have hi₀ne : (R ℓ i₀).Nonempty := by
    by_contra hi
    rw [Set.not_nonempty_iff_eq_empty.mp hi, measure_empty] at hi₀
    exact lt_irrefl _ hi₀
  obtain ⟨p₀, hp₀⟩ := hi₀ne
  have hstemdir := (h.piece_direction hθ hv ((hR ℓ i₀).2 hp₀)).2
  refine ⟨R ℓ, i₀, fun i => ⟨(hR ℓ i).1, (hR ℓ i).2.trans (hUZ ℓ i)⟩,
    ⟨p₀, hp₀⟩, ?_, ?_, hBrR ℓ⟩
  · intro i hi
    have hh := hmassR ℓ i hi
    simpa only [cost, if_pos (hi.mono (hR ℓ i).2)] using hh
  · intro i hi
    obtain ⟨p, hp⟩ := hi
    have hdir := (h.piece_direction hθ hv ((hR ℓ i).2 hp)).2
    have hh := wz_measurable_angular_selection.pd_triangle (v i)
      (wz_balanced_cluster_cover.W θ (ℓ : PacketLabel).1) (v i₀)
    have he : pd (wz_balanced_cluster_cover.W θ (ℓ : PacketLabel).1) (v i₀) =
        pd (v i₀) (wz_balanced_cluster_cover.W θ (ℓ : PacketLabel).1) :=
      wz_measurable_angular_selection.pd_comm _ _
    rw [he] at hh
    linarith


/-- Uniform original row masses pay the occupied-row budget after a known
mass retention. -/
theorem packet_pruning_budget {n : ℕ} {Y Z : Fin n → Set V}
    (S : Finset (Fin n)) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZfin : ∀ i, volume (Z i) ≠ ∞)
    {C base mass t : ℝ} (ht : 0 ≤ t)
    (hrows : ∀ i ∈ S, O base ≤ volume (Y i))
    (hret : O t * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (hbudget : C*mass ≤ t*base/4) :
    O (C*S.card*mass) ≤ (1/4 : ENNReal)*∑ i, volume (Z i) := by
  have hrow : (S.card : ℝ)*base ≤ ∑ i, volume.real (Y i) := by
    calc
      _ = ∑ _i ∈ S, base := by simp
      _ ≤ ∑ i ∈ S, volume.real (Y i) := Finset.sum_le_sum fun i hi =>
        (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).mp (hrows i hi)
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hret' : t*(∑ i, volume.real (Y i)) ≤ ∑ i, volume.real (Z i) := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hZfin i)) hret
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
      ENNReal.toReal_sum (fun i _ => hYfin i), ENNReal.toReal_sum (fun i _ => hZfin i),
      Measure.real] using hh
  have hreal : C*S.card*mass ≤ (1/4:ℝ)*(∑ i, volume.real (Z i)) := by
    calc
      _ = (C*mass)*(S.card : ℝ) := by ring
      _ ≤ (t*base/4)*(S.card : ℝ) := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
      _ = (1/4:ℝ)*t*((S.card : ℝ)*base) := by ring
      _ ≤ (1/4:ℝ)*t*(∑ i, volume.real (Y i)) := by gcongr
      _ = (1/4:ℝ)*(t*∑ i, volume.real (Y i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hret' (by norm_num)
  apply (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (by norm_num)
    (ENNReal.sum_ne_top.mpr (fun i _ => hZfin i)))).mpr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun i _ => hZfin i), Measure.real] using hreal

/-- The packet-pruning interface with only scalar budgets and original uniform
row density as inputs. -/
theorem exists_massful_broad_packet_of_retention {n : ℕ} {β d θ mass base t : ℝ}
    {x v : Fin n → V} {Y Z : Fin n → Set V}
    {F : V → Finset (Finset (Fin n))} {a : V → Finset (Fin n) → Fin n}
    (h : PacketRefinement β d θ v Y Z F a)
    (hd : 0 < d) (hθ : 0 < θ) (hdθ : d ≤ θ) (hmass : 0 ≤ mass) (ht : 0 ≤ t)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hrows : ∀ i, (Y i).Nonempty → O base ≤ volume (Y i))
    (hpos : 0 < ∑ i, volume (Z i))
    (hret : O t * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (hbudget : (2*6^3*22^3 : ℝ)*mass ≤ t*base/4) :
    ∃ R : Fin n → Set V, ∃ i₀ : Fin n,
      (∀ i, MeasurableSet (R i) ∧ R i ⊆ Z i) ∧ (R i₀).Nonempty ∧
      (∀ i, (R i).Nonempty → O mass ≤ volume (R i)) ∧
      (∀ i, (R i).Nonempty → pd (v i) (v i₀) ≤ 8*θ) ∧
      ∀ p u r, d ≤ r → q n {i | p ∈ R i ∧ pd (v i) u ≤ r} ≤
        8*(r/θ)^β*q n {i | p ∈ R i} := by
  classical
  let S := Finset.univ.filter (fun i => (Y i).Nonempty)
  have hfin (i : Fin n) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hYT i)
    (wz_flat_cluster_slab_filling.tube_volume_ne_top d (x i) (v i))
  have hZfin (i : Fin n) : volume (Z i) ≠ ∞ :=
    measure_ne_top_of_subset (h.1 i).2 (hfin i)
  apply exists_massful_broad_packet h hd hθ hdθ hmass hv
    (fun i => (h.1 i).2.trans (hYT i)) S _ hpos
    (packet_pruning_budget S hfin hZfin ht
      (fun i hi => hrows i (Finset.mem_filter.mp hi).2) hret hbudget)
  intro i hi
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, (h.1 i).2 hp⟩)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
