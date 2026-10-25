/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit 525ce8d3c8ed1d02854b5f6c797e220d2ac13ddd, file Submission/Obl/k4_horizontal_wide_interval_return/Native/ShortBound.lean.
Namespace/imports renamed; velocity nullness dependency minimized. Earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Short
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.VelocityNull

set_option autoImplicit false

/-!
# Mass of the bad incidences of the short comparison

`short_bad_le`: the light entries cost their reference sums divided by `K₁`; the heavy pairs with
far key graphs cost the matching bound of `key_pairs_abstract`, summed over the slots and the
keys of the key box.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

open scoped Classical in
/-- Reference sum of the block entries of positive mass. -/
def blockSum (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m : ℝ) (KB : Finset (Fin 3 → ℤ)) : ℝ :=
  ∑ i, ∑ κ ∈ KB.filter (fun κ => 0 < L.ρs (blockLab cfg k s L m i κ ×ˢ
      cfg.I (cfg.T k s) (cfg.j k s i))),
    keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ

open scoped Classical in
/-- Reference sum of the piece entries of positive mass of one layer. -/
def pieceSum (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m : ℝ) (KB : Finset (Fin 3 → ℤ)) (h : Fin 3) : ℝ :=
  ∑ i : Fin (L.np h), ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB.filter (fun κ =>
      0 < L.ρs (pieceLab cfg k s L m h i jj κ ×ˢ cfg.I (cfg.T k s) jj)),
    keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ

/-! ### Light entries -/

theorem shortBound_keyRef_nonneg (cfg : Data α) (k : ℕ) {χ m q a : ℝ} (hχ : 0 ≤ χ)
    (hm : 0 ≤ m) (hq : 0 ≤ q) (ha : 0 ≤ a) (κ : Fin 3 → ℤ) : 0 ≤ keyRef cfg k χ m q a κ := by
  unfold keyRef
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hq hχ) hm) (Real.rpow_nonneg ha _))
    ENNReal.toReal_nonneg

/-- A light entry costs its reference over `K₁` when it has positive mass, nothing otherwise. -/
theorem shortBound_light_entry_le (ρ : Measure (α × ℝ)) (E : Set (α × ℝ)) (T K₁ : ℝ) :
    ρ {p | p ∈ E ∧ ¬ Heavy ρ E T K₁} ≤ if 0 < ρ E then ENNReal.ofReal (T / K₁) else 0 := by
  by_cases hh : Heavy ρ E T K₁
  · have he : {p | p ∈ E ∧ ¬ Heavy ρ E T K₁} = ∅ := by
      ext p; simp [hh]
    rw [he, measure_empty]
    exact zero_le
  · have he : {p | p ∈ E ∧ ¬ Heavy ρ E T K₁} = E := by
      ext p; simp [hh]
    rw [he]
    by_cases hpos : 0 < ρ E
    · rw [ite_eq_left hpos]
      rcases le_or_gt (ENNReal.ofReal (T / K₁)) (ρ E) with h | h
      · exact absurd ⟨h, hpos⟩ hh
      · exact h.le
    · rw [ite_eq_right hpos]
      exact le_of_not_gt hpos

theorem shortBound_sum_ite_ofReal {ι : Type*} (KB : Finset ι) (P : ι → Prop) [DecidablePred P]
    (T : ι → ℝ) {K₁ : ℝ} (hK₁ : 0 ≤ K₁) (hT : ∀ κ, 0 ≤ T κ) :
    ∑ κ ∈ KB, (if P κ then ENNReal.ofReal (T κ / K₁) else 0) =
      ENNReal.ofReal ((∑ κ ∈ KB.filter P, T κ) / K₁) := by
  rw [← Finset.sum_filter, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg]
  intro κ _
  exact div_nonneg (hT κ) hK₁

theorem shortBound_sum_ofReal_div {ι : Type*} (S : Finset ι) (f : ι → ℝ) {K₁ : ℝ}
    (hK₁ : 0 ≤ K₁) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ S, ENNReal.ofReal (f i / K₁) = ENNReal.ofReal ((∑ i ∈ S, f i) / K₁) := by
  rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact div_nonneg (hf i) hK₁

/-- **Light block entries.** -/
theorem shortBound_light_blocks_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (m K₁ : ℝ)
    (KB : Finset (Fin 3 → ℤ)) (hK₁ : 0 ≤ K₁)
    (hT : ∀ κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) :
    L.ρs (⋃ i, ⋃ κ ∈ KB, {p | p ∈ blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ∧
      ¬ blockHeavy cfg k s L m K₁ i κ}) ≤ ENNReal.ofReal (blockSum cfg k s L m KB / K₁) := by
  calc _ ≤ ∑ i, ∑ κ ∈ KB, L.ρs {p | p ∈ blockLab cfg k s L m i κ ×ˢ
          cfg.I (cfg.T k s) (cfg.j k s i) ∧ ¬ blockHeavy cfg k s L m K₁ i κ} :=
        (measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ i, ∑ κ ∈ KB, (if 0 < L.ρs (blockLab cfg k s L m i κ ×ˢ
          cfg.I (cfg.T k s) (cfg.j k s i)) then
          ENNReal.ofReal (keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ / K₁) else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun κ _ =>
          shortBound_light_entry_le _ _ _ _
    _ = ∑ i, ENNReal.ofReal ((∑ κ ∈ KB.filter (fun κ => 0 < L.ρs (blockLab cfg k s L m i κ ×ˢ
          cfg.I (cfg.T k s) (cfg.j k s i))),
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) / K₁) :=
        Finset.sum_congr rfl fun i _ => shortBound_sum_ite_ofReal _ _ _ hK₁ hT
    _ = ENNReal.ofReal (blockSum cfg k s L m KB / K₁) := by
        rw [shortBound_sum_ofReal_div _ _ hK₁ (fun i => Finset.sum_nonneg fun κ _ => hT κ)]
        rfl

/-- **Light piece entries.** -/
theorem shortBound_light_pieces_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (m K₁ : ℝ)
    (KB : Finset (Fin 3 → ℤ)) (hK₁ : 0 ≤ K₁)
    (hT : ∀ h κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ) :
    L.ρs (⋃ h, ⋃ i, ⋃ jj, ⋃ κ ∈ KB, {p | p ∈ pieceLab cfg k s L m h i jj κ ×ˢ
      cfg.I (cfg.T k s) jj ∧ ¬ pieceHeavy cfg k s L m K₁ h i jj κ}) ≤
      ∑ h : Fin 3, ENNReal.ofReal (pieceSum cfg k s L m KB h / K₁) := by
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  calc _ ≤ ∑ i, ∑ jj, ∑ κ ∈ KB, L.ρs {p | p ∈ pieceLab cfg k s L m h i jj κ ×ˢ
          cfg.I (cfg.T k s) jj ∧ ¬ pieceHeavy cfg k s L m K₁ h i jj κ} :=
        (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun jj _ =>
            measure_biUnion_finset_le _ _))
    _ ≤ ∑ i, ∑ jj, ∑ κ ∈ KB, (if 0 < L.ρs (pieceLab cfg k s L m h i jj κ ×ˢ
          cfg.I (cfg.T k s) jj) then
          ENNReal.ofReal (keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ / K₁)
          else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun jj _ =>
          Finset.sum_le_sum fun κ _ => shortBound_light_entry_le _ _ _ _
    _ = ∑ i, ∑ jj, ENNReal.ofReal ((∑ κ ∈ KB.filter (fun κ => 0 < L.ρs
          (pieceLab cfg k s L m h i jj κ ×ˢ cfg.I (cfg.T k s) jj)),
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ) / K₁) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun jj _ =>
          shortBound_sum_ite_ofReal _ _ _ hK₁ (hT h)
    _ = ∑ i, ENNReal.ofReal ((∑ jj, ∑ κ ∈ KB.filter (fun κ => 0 < L.ρs
          (pieceLab cfg k s L m h i jj κ ×ˢ cfg.I (cfg.T k s) jj)),
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ) / K₁) :=
        Finset.sum_congr rfl fun i _ =>
          shortBound_sum_ofReal_div _ _ hK₁ (fun jj => Finset.sum_nonneg fun κ _ => hT h κ)
    _ = ENNReal.ofReal (pieceSum cfg k s L m KB h / K₁) := by
        rw [shortBound_sum_ofReal_div _ _ hK₁ (fun i => Finset.sum_nonneg fun jj _ =>
          Finset.sum_nonneg fun κ _ => hT h κ)]
        rfl

/-! ### Heavy pairs, regrouped by slot and key -/

/-- Heavy blocks of the slot `jj` on the key `κ`. -/
abbrev ShortHeavyBlocks (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m K₁ : ℝ) (jj : Fin (2 ^ cfg.T k s))
    (κ : Fin 3 → ℤ) : Type :=
  {i : Fin (cfg.n k s) // cfg.j k s i = jj ∧ blockHeavy cfg k s L m K₁ i κ}

/-- Heavy layer-0 pieces of the slot `jj` on the key `κ`. -/
abbrev ShortHeavyPieces (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m K₁ : ℝ) (jj : Fin (2 ^ cfg.T k s))
    (κ : Fin 3 → ℤ) : Type :=
  {i₀ : Fin (L.np 0) // pieceHeavy cfg k s L m K₁ 0 i₀ jj κ}

open scoped Classical in
/-- The bad heavy pairs, regrouped by slot and key. -/
theorem shortBound_pairs_subset (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (m K₁ Mst : ℝ)
    (KB : Finset (Fin 3 → ℤ)) :
    (⋃ i, ⋃ i₀, ⋃ κ ∈ KB, {p | p ∈ (blockLab cfg k s L m i κ ∩ pieceLab cfg k s L m 0 i₀
      (cfg.j k s i) κ) ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ∧ blockHeavy cfg k s L m K₁ i κ ∧
      pieceHeavy cfg k s L m K₁ 0 i₀ (cfg.j k s i) κ ∧ pairBad cfg k s L m Mst i i₀ κ}) ⊆
    ⋃ jj : Fin (2 ^ cfg.T k s), ⋃ κ ∈ KB, ⋃ i : ShortHeavyBlocks cfg k s L m K₁ jj κ,
      ⋃ i₀ ∈ (Finset.univ : Finset (ShortHeavyPieces cfg k s L m K₁ jj κ)).filter
        (fun i₀ => ∃ e, Mst ≤ |blockKeyCoeff (cfg.F k s i.1) (cfg.N k ^ (-s)) χ m
          (slotLen cfg k s) (slotStart cfg k s jj) κ e -
          sheetKeyCoeff (L.G 0 i₀.1) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
            (slotStart cfg k s jj) κ e|),
      (blockLab cfg k s L m i.1 κ ∩ pieceLab cfg k s L m 0 i₀.1 jj κ) ×ˢ
        Icc (slotStart cfg k s jj) (slotStart cfg k s jj + slotLen cfg k s) := by
  intro p hp
  simp only [mem_iUnion] at hp
  obtain ⟨i, i₀, κ, hκ, hpmem, hbh, hph, hbad⟩ := hp
  simp only [mem_iUnion]
  refine ⟨cfg.j k s i, κ, hκ, ⟨i, rfl, hbh⟩, ⟨i₀, hph⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩, ?_⟩
  rw [I_eq_slot] at hpmem
  exact hpmem

open scoped Classical in
theorem shortBound_pairs_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (m K₁ Mst : ℝ)
    (KB : Finset (Fin 3 → ℤ)) :
    L.ρs (⋃ i, ⋃ i₀, ⋃ κ ∈ KB, {p | p ∈ (blockLab cfg k s L m i κ ∩ pieceLab cfg k s L m 0 i₀
      (cfg.j k s i) κ) ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ∧ blockHeavy cfg k s L m K₁ i κ ∧
      pieceHeavy cfg k s L m K₁ 0 i₀ (cfg.j k s i) κ ∧ pairBad cfg k s L m Mst i i₀ κ}) ≤
    ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, ∑ i : ShortHeavyBlocks cfg k s L m K₁ jj κ,
      ∑ i₀ ∈ (Finset.univ : Finset (ShortHeavyPieces cfg k s L m K₁ jj κ)).filter
        (fun i₀ => ∃ e, Mst ≤ |blockKeyCoeff (cfg.F k s i.1) (cfg.N k ^ (-s)) χ m
          (slotLen cfg k s) (slotStart cfg k s jj) κ e -
          sheetKeyCoeff (L.G 0 i₀.1) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
            (slotStart cfg k s jj) κ e|),
      L.ρs ((blockLab cfg k s L m i.1 κ ∩ pieceLab cfg k s L m 0 i₀.1 jj κ) ×ˢ
        Icc (slotStart cfg k s jj) (slotStart cfg k s jj + slotLen cfg k s)) := by
  refine (measure_mono (shortBound_pairs_subset cfg k s L m K₁ Mst KB)).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun jj _ => ?_)
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact measure_biUnion_finset_le _ _

open scoped Classical in
/-- The heavy blocks over slots and keys carry at most the block reference sum. -/
theorem shortBound_block_count_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (m K₁ : ℝ)
    (KB : Finset (Fin 3 → ℤ))
    (hT : ∀ κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) :
    ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
      (Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) : ℝ) *
        keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ ≤ blockSum cfg k s L m KB := by
  have e1 : ∀ jj κ, (Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) : ℝ) *
      keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ =
      ∑ i, if cfg.j k s i = jj ∧ blockHeavy cfg k s L m K₁ i κ then
        keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0 := by
    intro jj κ
    rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc _ = ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, ∑ i,
        (if cfg.j k s i = jj ∧ blockHeavy cfg k s L m K₁ i κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) :=
        Finset.sum_congr rfl fun jj _ => Finset.sum_congr rfl fun κ _ => e1 jj κ
    _ = ∑ κ ∈ KB, ∑ jj : Fin (2 ^ cfg.T k s), ∑ i,
        (if cfg.j k s i = jj ∧ blockHeavy cfg k s L m K₁ i κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := Finset.sum_comm
    _ = ∑ κ ∈ KB, ∑ i, ∑ jj : Fin (2 ^ cfg.T k s),
        (if cfg.j k s i = jj ∧ blockHeavy cfg k s L m K₁ i κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) :=
        Finset.sum_congr rfl fun κ _ => Finset.sum_comm
    _ = ∑ κ ∈ KB, ∑ i, (if blockHeavy cfg k s L m K₁ i κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := by
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [ite_and]
        exact Fintype.sum_ite_eq _ _
    _ = ∑ i, ∑ κ ∈ KB, (if blockHeavy cfg k s L m K₁ i κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := Finset.sum_comm
    _ ≤ ∑ i, ∑ κ ∈ KB, (if 0 < L.ρs (blockLab cfg k s L m i κ ×ˢ
          cfg.I (cfg.T k s) (cfg.j k s i)) then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun κ _ => ?_
        by_cases hh : blockHeavy cfg k s L m K₁ i κ
        · rw [ite_eq_left hh, ite_eq_left hh.2]
        · rw [ite_eq_right hh]
          split_ifs
          · exact hT κ
          · exact le_refl 0
    _ = blockSum cfg k s L m KB := by
        unfold blockSum
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_filter _ _).symm

open scoped Classical in
/-- The heavy layer-0 pieces over slots and keys carry at most the layer-0 reference sum. -/
theorem shortBound_piece_count_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (hdepth0 : depth 0 = s)
    (m K₁ : ℝ) (KB : Finset (Fin 3 → ℤ))
    (hT : ∀ κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) :
    ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
      (Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
        keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ ≤ pieceSum cfg k s L m KB 0 := by
  have e1 : ∀ jj κ, (Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
      keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ =
      ∑ i₀, if pieceHeavy cfg k s L m K₁ 0 i₀ jj κ then
        keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0 := by
    intro jj κ
    rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc _ = ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, ∑ i₀,
        (if pieceHeavy cfg k s L m K₁ 0 i₀ jj κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) :=
        Finset.sum_congr rfl fun jj _ => Finset.sum_congr rfl fun κ _ => e1 jj κ
    _ = ∑ jj : Fin (2 ^ cfg.T k s), ∑ i₀, ∑ κ ∈ KB,
        (if pieceHeavy cfg k s L m K₁ 0 i₀ jj κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) :=
        Finset.sum_congr rfl fun jj _ => Finset.sum_comm
    _ = ∑ i₀, ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
        (if pieceHeavy cfg k s L m K₁ 0 i₀ jj κ then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := Finset.sum_comm
    _ ≤ ∑ i₀, ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
        (if 0 < L.ρs (pieceLab cfg k s L m 0 i₀ jj κ ×ˢ cfg.I (cfg.T k s) jj) then
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ else 0) := by
        refine Finset.sum_le_sum fun i₀ _ => Finset.sum_le_sum fun jj _ =>
          Finset.sum_le_sum fun κ _ => ?_
        by_cases hh : pieceHeavy cfg k s L m K₁ 0 i₀ jj κ
        · rw [ite_eq_left hh, ite_eq_left hh.2]
        · rw [ite_eq_right hh]
          split_ifs
          · exact hT κ
          · exact le_refl 0
    _ = pieceSum cfg k s L m KB 0 := by
        unfold pieceSum
        rw [hdepth0]
        exact Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun jj _ =>
          (Finset.sum_filter _ _).symm

/-! ### One slot key -/

/-- A set of incidences of positive mass, horizontal almost everywhere, has a horizontal
label. -/
theorem shortBound_exists_horiz {ρ : Measure (α × ℝ)} {b : α → Fin 6 → ℝ} {ζ : ℝ}
    (hnull : ρ (horizSet b ζ)ᶜ = 0) {S : Set α} {I : Set ℝ} (hpos : 0 < ρ (S ×ˢ I)) :
    ∃ l ∈ S, |b l 4 + b l 0| ≤ ζ := by
  by_contra hcon
  have hsub : S ×ˢ I ⊆ (horizSet b ζ)ᶜ := by
    rintro p ⟨hp1, -⟩ hph
    exact hcon ⟨p.1, hp1, hph⟩
  have h0 := measure_mono_null hsub hnull
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Block key coefficients are bounded**, from one label of the block entry. -/
theorem shortBound_block_coeff_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D R' : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    {m Xb Lv B : ℝ} (hm : 0 < m) (hK1 : 1 ≤ cfg.K k)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hXb1 : 1 ≤ Xb) (hKa : cfg.K k * cfg.N k ^ (-s) ≤ 1)
    (hN : 0 < cfg.N k) (i : Fin (cfg.n k s)) (κ : Fin 3 → ℤ)
    (hκb : |(κ 0 : ℝ) * χ| ≤ Lv ∧ |(κ 1 : ℝ) * χ| ≤ Lv ∧ |(κ 2 : ℝ) * m| ≤ Lv)
    (hne : (blockLab cfg k s L m i κ).Nonempty)
    (hBblk : 8 * (12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
      (2 + 4 * Lv + 3 * m) / cfg.N k ^ (-s)) ≤ B) :
    ∀ e, |blockKeyCoeff (cfg.F k s i) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
      (slotStart cfg k s (cfg.j k s i)) κ e| ≤ B := by
  obtain ⟨l, ⟨hlB, hlG⟩, -⟩ := hne
  obtain ⟨i', hli'⟩ := mem_iUnion.mp hlG
  have hbl : ∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε := (L.mem_bins hli').2.2.2
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  obtain ⟨hs0, hs1⟩ := slot_unit cfg k s (cfg.j k s i)
  have hq1 : slotLen cfg k s ≤ 1 := by linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hstart0 := shortDefs_slot_time_unit cfg k s (cfg.j k s i) h0
  have hstart := shortDefs_slot_time_mem cfg k s (cfg.j k s i) h0
  rw [mul_zero, add_zero] at hstart0 hstart
  obtain ⟨Lc, hF, hL3, hL12⟩ := hB.affine i
  have hqe : ((2 : ℝ) ^ cfg.T k s)⁻¹ = slotLen cfg k s := rfl
  rw [hqe] at hL3 hL12
  have hΛ : 1 ≤ 1 + cfg.N k ^ (-s) / slotLen cfg k s ^ 2 := by
    have : 0 ≤ cfg.N k ^ (-s) / slotLen cfg k s ^ 2 := by positivity
    linarith
  have haq : cfg.N k ^ (-s) / slotLen cfg k s ≤ cfg.N k ^ (-s) / slotLen cfg k s ^ 2 :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by nlinarith)
  have hK0 : 0 ≤ cfg.K k := by linarith
  have h12 := hL12 l hlB _ hstart
  have hfit0 := (hB.fit i l hlB _ hstart).1
  rw [eval_horizontalForm hF, blockGraph_eq hF] at hfit0
  have hLb := block_affine_bound (Lc := Lc) (K := cfg.K k)
    (Λ := 1 + cfg.N k ^ (-s) / slotLen cfg k s ^ 2) (a := cfg.N k ^ (-s)) (Xb := Xb)
    (x₁ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 1)
    (x₂ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 2)
    (x₃ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 3)
    (t := slotStart cfg k s (cfg.j k s i))
    hK1 hΛ hXb1 hstart0 hKa hL3
    (h12.trans (mul_le_mul_of_nonneg_left (by linarith) hK0))
    (shortDefs_coord_bound hbl hXb hstart0 0 3)
    (shortDefs_coord_bound hbl hXb hstart0 1 4)
    (shortDefs_coord_bound hbl hXb hstart0 2 5)
    hfit0
  have hcoef := blockKeyCoeff_bound hF hLb (χ := χ) (m := m) (q := slotLen cfg k s)
    (t₀ := slotStart cfg k s (cfg.j k s i)) (Zb := 2 * Lv) (Yb := 2 * Lv + 3 * m) ha κ
    (fun τ hτ => by
      have ht := shortDefs_slot_time_unit cfg k s (cfg.j k s i) hτ
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    (fun τ hτ => by
      have ht := shortDefs_slot_time_unit cfg k s (cfg.j k s i) hτ
      have htabs : |slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      unfold domZ
      calc |(κ 1 : ℝ) * χ + (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) *
            ((κ 0 : ℝ) * χ)|
          ≤ |(κ 1 : ℝ) * χ| + |(slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) *
            ((κ 0 : ℝ) * χ)| := abs_add_le _ _
        _ = |(κ 1 : ℝ) * χ| + |slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ| *
            |(κ 0 : ℝ) * χ| := by
              rw [abs_mul (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ)]
        _ ≤ Lv + 1 * Lv :=
            add_le_add hκb.2.1 (mul_le_mul htabs hκb.1 (abs_nonneg _) zero_le_one)
        _ = 2 * Lv := by ring)
    (fun τ hτ y hy => by
      unfold domY
      have h1 : |2 * m * (y - 1 / 4)| ≤ 3 * m := by
        rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * m)]
        have : |y - 1 / 4| ≤ 5 / 4 := by
          rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
        nlinarith
      have h2 : |slotLen cfg k s * τ * ((κ 1 : ℝ) * χ)| ≤ Lv := by
        rw [abs_mul]
        have hqτ : |slotLen cfg k s * τ| ≤ 1 := by
          rw [abs_of_nonneg (mul_nonneg hq0.le hτ.1)]; nlinarith [hτ.1, hτ.2]
        calc |slotLen cfg k s * τ| * |(κ 1 : ℝ) * χ| ≤ 1 * Lv :=
              mul_le_mul hqτ hκb.2.1 (abs_nonneg _) zero_le_one
          _ = Lv := one_mul _
      have h3 := abs_sub ((κ 2 : ℝ) * m + 2 * m * (y - 1 / 4))
        (slotLen cfg k s * τ * ((κ 1 : ℝ) * χ))
      have h4 := abs_add_le ((κ 2 : ℝ) * m) (2 * m * (y - 1 / 4))
      linarith [hκb.2.2])
  intro e
  calc _ ≤ _ := hcoef e
    _ = 8 * (12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
          (2 + 4 * Lv + 3 * m) / cfg.N k ^ (-s)) := by ring
    _ ≤ B := hBblk

/-- **Sheet key coefficients are bounded**, from one horizontal label of the piece entry. -/
theorem shortBound_sheet_coeff_le (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) {m ζ B : ℝ} (hχ : 0 < χ)
    (hD : 0 < D) (hm : 0 < m)
    (hdrift : ζ + χ ≤ D / 4) (hsmallD : 4 * m + slotLen cfg k s * (ζ + χ) ≤ 4 * D)
    (hN : 0 < cfg.N k) (h : Fin 3) (i : Fin (L.np h)) (jj : Fin (2 ^ cfg.T k s))
    (κ : Fin 3 → ℤ) {l : α} (hl : l ∈ pieceLab cfg k s L m h i jj κ)
    (hlζ : |cfg.b k l 4 + cfg.b k l 0| ≤ ζ)
    (hBsh : 8 * (11 * (160 * cfg.N k ^ ε) / cfg.N k ^ (-s)) ≤ B) :
    ∀ e, |sheetKeyCoeff (L.G h i) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
      (slotStart cfg k s jj) κ e| ≤ B := by
  obtain ⟨hlC, hκ⟩ := hl
  have hκ' : slotKey (cfg.b k) χ m (slotStart cfg k s jj) l = κ := hκ
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  have hH := CompareSheets.sheetCoeff_bound (L.degree h i) (L.strip h i)
  have hcoef := sheetKeyCoeff_bound (L.degree h i) hD hH ha κ (χ := χ) (m := m)
    (q := slotLen cfg k s) (t₀ := slotStart cfg k s jj)
    (fun τ hτ => by
      have ht := shortDefs_slot_time_unit cfg k s jj hτ
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    (fun τ hτ y hy => by
      have ht := shortDefs_slot_time_unit cfg k s jj hτ
      have hηl : etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D
          (slotStart cfg k s jj + slotLen cfg k s * τ)
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4) ∈
            Icc (1 / 4 : ℝ) 1 :=
        L.etaFun_mem (p := (l, slotStart cfg k s jj + slotLen cfg k s * τ)) hlC hχ hD ht hlζ
          hdrift
      have hY := key_Y_near hχ hm.ne' hq0.le hκ' hlζ hτ
      have hsl := sliceY_mem (cfg.b k) m (slotStart cfg k s jj) l
      have hdY : |domY χ m (slotLen cfg k s) κ τ y -
          domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l)| ≤
          4 * m := by
        have e : domY χ m (slotLen cfg k s) κ τ y -
            domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l) =
            2 * m * (y - sliceY (cfg.b k) m (slotStart cfg k s jj) l) := by
          unfold domY; ring
        rw [e, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * m)]
        have : |y - sliceY (cfg.b k) m (slotStart cfg k s jj) l| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hsl.1, hsl.2]
        nlinarith
      have hdiff : |domY χ m (slotLen cfg k s) κ τ y -
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)| ≤
          4 * m + slotLen cfg k s * (ζ + χ) := by
        have h1 := abs_sub_le (domY χ m (slotLen cfg k s) κ τ y)
          (domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l))
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)
        rw [abs_sub_comm (domY χ m (slotLen cfg k s) κ τ
          (sliceY (cfg.b k) m (slotStart cfg k s jj) l))] at h1
        linarith
      have hdη := etaFun_sub (y₀ := (L.qp h i 2 : ℝ) * D) (v := -((L.qp h i 1 : ℝ) * χ)) hD
        (slotStart cfg k s jj + slotLen cfg k s * τ) (domY χ m (slotLen cfg k s) κ τ y)
        (slotStart cfg k s jj + slotLen cfg k s * τ)
        (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)
      simp only [sub_self, abs_zero, mul_zero, add_zero] at hdη
      have h1 : |domY χ m (slotLen cfg k s) κ τ y -
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)| /
          (4 * D) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hdη' := hdη.trans h1
      rw [abs_le] at hdη' ⊢
      obtain ⟨hη1, hη2⟩ := hηl
      constructor <;> linarith [hdη'.1, hdη'.2])
  intro e
  exact (hcoef e).trans hBsh

open scoped Classical in
/-- **The bad heavy pairs of one slot and one key**, from `key_pairs_abstract`. -/
theorem shortBound_key_le {η R₀ : ℝ} (cfg : Data α)
    (hPC : ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (yf : α → ℝ), Measurable yf →
      ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
        (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α)
        (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
        (δ Mst A B w : ℝ),
        (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
        (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
        (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
        0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
        0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
        (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
        (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
        (∀ i (x : ℝ), ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₁ i * w)) →
        (∀ j (x : ℝ), ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₂ j * w)) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ cfg.d) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ cfg.d) →
        (∀ i j, ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → yf p.1 ∈ closeSet (F₁ i) (F₂ j) δ) →
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
            ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
          ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)))
    (k : ℕ) (s : ℝ) {ε R χ D R' : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hdepth0 : depth 0 = s)
    (hB : BlocksAt cfg k s R') (hb : Measurable (cfg.b k))
    (hπ : MeasureTheory.IsProbabilityMeasure (cfg.π k)) (hρμ : L.ρs ≤ cfg.μ k)
    [IsFiniteMeasure L.ρs]
    {m K₁ Mst r v' Rc s₁ ζ Lv Xb B δ A w : ℝ}
    (hχv : χ = cfg.N k ^ (-v')) (hN : 0 < cfg.N k)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' v')
    (jj : Fin (2 ^ cfg.T k s)) (κ : Fin 3 → ℤ)
    (hn : KeyNum (cfg.N k) (cfg.K k) cfg.d r v' Rc s₁ (slotStart cfg k s jj) (slotLen cfg k s)
        m ζ Lv (cfg.N k ^ (-s)) Xb K₁ B
        (cfg.K k + 12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
          (2 * χ + slotLen cfg k s * (ζ + χ)) / cfg.N k ^ (-s))
        ((cfg.N k ^ ε * cfg.N k ^ (-depth 0) +
          7 * (160 * cfg.N k ^ ε) * (slotLen cfg k s * (ζ + χ)) / (4 * D)) / cfg.N k ^ (-s))
        δ Mst A w η R₀ κ)
    (hκb : |(κ 0 : ℝ) * χ| ≤ Lv ∧ |(κ 1 : ℝ) * χ| ≤ Lv ∧ |(κ 2 : ℝ) * m| ≤ Lv)
    (hnull : L.ρs (horizSet (cfg.b k) ζ)ᶜ = 0)
    (hχ : 0 < χ) (hD : 0 < D) (hm : 0 < m) (hK1 : 1 ≤ cfg.K k)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hXb1 : 1 ≤ Xb) (hKa : cfg.K k * cfg.N k ^ (-s) ≤ 1)
    (hdrift : ζ + χ ≤ D / 4) (hsmallD : 4 * m + slotLen cfg k s * (ζ + χ) ≤ 4 * D)
    (hBblk : 8 * (12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
      (2 + 4 * Lv + 3 * m) / cfg.N k ^ (-s)) ≤ B)
    (hBsh : 8 * (11 * (160 * cfg.N k ^ ε) / cfg.N k ^ (-s)) ≤ B) :
    (∑ i : ShortHeavyBlocks cfg k s L m K₁ jj κ,
      ∑ i₀ ∈ (Finset.univ : Finset (ShortHeavyPieces cfg k s L m K₁ jj κ)).filter
        (fun i₀ => ∃ e, Mst ≤ |blockKeyCoeff (cfg.F k s i.1) (cfg.N k ^ (-s)) χ m
          (slotLen cfg k s) (slotStart cfg k s jj) κ e -
          sheetKeyCoeff (L.G 0 i₀.1) (cfg.N k ^ (-s)) χ m (slotLen cfg k s)
            (slotStart cfg k s jj) κ e|),
        L.ρs ((blockLab cfg k s L m i.1 κ ∩ pieceLab cfg k s L m 0 i₀.1 jj κ) ×ˢ
          Icc (slotStart cfg k s jj) (slotStart cfg k s jj + slotLen cfg k s))) ≤
      ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
        ((Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) +
          Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ)) := by
  have := hπ
  subst hχv
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  by_cases hπ0 : cfg.π k {w | ⌊w / cfg.N k ^ (-v')⌋ = κ 0} = 0
  · -- a null velocity bin carries no heavy block entry
    have hμ0 : cfg.μ k {p : α × ℝ | ⌊cfg.b k p.1 3 / cfg.N k ^ (-v')⌋ = κ 0} = 0 :=
      velocityBin_null (hcap s₁ hn.hs₁0 hn.hs₁R) (κ 0) hπ0
    have : IsEmpty (ShortHeavyBlocks cfg k s L m K₁ jj κ) := by
      refine ⟨fun i => ?_⟩
      obtain ⟨i, -, hh⟩ := i
      have hsub : blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i) ⊆
          {p : α × ℝ | ⌊cfg.b k p.1 3 / cfg.N k ^ (-v')⌋ = κ 0} := by
        rintro p ⟨⟨-, hκ⟩, -⟩
        have hκ' : slotKey (cfg.b k) (cfg.N k ^ (-v')) m
            (slotStart cfg k s (cfg.j k s i)) p.1 = κ := hκ
        have h0 := congrFun hκ' 0
        simpa [slotKey] using h0
      have h0 : L.ρs (blockLab cfg k s L m i κ ×ˢ cfg.I (cfg.T k s) (cfg.j k s i)) = 0 :=
        measure_mono_null hsub (le_antisymm ((hρμ _).trans hμ0.le) bot_le)
      have hpos := hh.2
      rw [h0] at hpos
      exact lt_irrefl 0 hpos
    rw [Fintype.sum_empty]
    exact zero_le
  · have hπfin : cfg.π k {w | ⌊w / cfg.N k ^ (-v')⌋ = κ 0} ≠ ⊤ := measure_ne_top _ _
    have hTpos : 0 < keyRef cfg k (cfg.N k ^ (-v')) m (slotLen cfg k s) (cfg.N k ^ (-s)) κ := by
      unfold keyRef
      exact mul_pos (mul_pos (mul_pos (mul_pos hq0 hχ) hm) (Real.rpow_pos_of_pos ha _))
        (ENNReal.toReal_pos hπ0 hπfin)
    have hsmall : slotLen cfg k s * (ζ + cfg.N k ^ (-v')) ≤ 4 * D := by linarith
    exact key_pairs_abstract hPC hb hρμ hn hcap
      (T := keyRef cfg k (cfg.N k ^ (-v')) m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) rfl hTpos
      hπfin hnull
      (ShortHeavyBlocks cfg k s L m K₁ jj κ) (ShortHeavyPieces cfg k s L m K₁ jj κ)
      (fun i => blockLab cfg k s L m i.1 κ) (fun i₀ => pieceLab cfg k s L m 0 i₀.1 jj κ)
      (fun i => blockKeyCoeff (cfg.F k s i.1) (cfg.N k ^ (-s)) (cfg.N k ^ (-v')) m
        (slotLen cfg k s) (slotStart cfg k s jj) κ)
      (fun i₀ => sheetKeyCoeff (L.G 0 i₀.1) (cfg.N k ^ (-s)) (cfg.N k ^ (-v')) m
        (slotLen cfg k s) (slotStart cfg k s jj) κ)
      (fun i => ((hB.sets i.1).2.1.inter (measurableSet_goodLab L)).inter
        (measurableSet_slotKey hb _ _ _ κ))
      (fun i₀ => (L.meas 0 i₀.1).inter (measurableSet_slotKey hb _ _ _ κ))
      (fun i i' hii' => Disjoint.mono
        (show blockLab cfg k s L m i.1 κ ⊆ cfg.A k s i.1 from
          fun l hl => (hB.sets i.1).2.2 hl.1.1)
        (show blockLab cfg k s L m i'.1 κ ⊆ cfg.A k s i'.1 from
          fun l hl => (hB.sets i'.1).2.2 hl.1.1)
        (hB.disj i.1 i'.1 (fun h => hii' (Subtype.ext h)) (i.2.1.trans i'.2.1.symm)))
      (fun i₀ i₀' hne => Disjoint.mono inter_subset_left inter_subset_left
        (L.disj 0 i₀.1 i₀'.1 (fun h => hne (Subtype.ext h))))
      (fun i => by
        obtain ⟨i, hij, hh⟩ := i
        have h1 := hh.1
        rw [hij, I_eq_slot] at h1
        exact h1)
      (fun i₀ => by
        obtain ⟨i₀, hh⟩ := i₀
        have h1 := hh.1
        rw [hdepth0, I_eq_slot] at h1
        exact h1)
      (fun i => by
        obtain ⟨i, hij, -⟩ := i
        intro l hl hζ
        have h1 := block_lab_graph cfg k s L hB hχ hm hK1 hXb hXb1 hKa hN i κ l hl hζ
        rw [hij] at h1
        exact h1)
      (fun i₀ l hl hζ =>
        piece_lab_graph cfg k s L hχ hD hm ha hXb hdrift hsmall 0 i₀.1 jj κ l hl hζ)
      (fun i e => by
        obtain ⟨i, hij, hh⟩ := i
        have hne : (blockLab cfg k s L m i κ).Nonempty :=
          (nonempty_of_measure_ne_zero hh.2.ne').fst
        have h1 := shortBound_block_coeff_le cfg k s L hB hm hK1 hXb hXb1 hKa hN i κ hκb hne
          hBblk e
        rw [hij] at h1
        exact h1)
      (fun i₀ e => by
        obtain ⟨i₀, hh⟩ := i₀
        obtain ⟨l, hl, hlζ⟩ := shortBound_exists_horiz hnull hh.2
        exact shortBound_sheet_coeff_le cfg k s L hχ hD hm hdrift hsmallD hN 0 i₀ jj κ hl hlζ
          hBsh e)

/-- **Mass of the short bad set.** -/
theorem short_bad_le {η R₀ : ℝ} (cfg : Data α)
    (hPC : ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (yf : α → ℝ), Measurable yf →
      ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
        (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α)
        (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
        (δ Mst A B w : ℝ),
        (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
        (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
        (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
        0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
        0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
        (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
        (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
        (∀ i (x : ℝ), ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₁ i * w)) →
        (∀ j (x : ℝ), ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₂ j * w)) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ cfg.d) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ cfg.d) →
        (∀ i j, ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → yf p.1 ∈ closeSet (F₁ i) (F₂ j) δ) →
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
            ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
          ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)))
    (k : ℕ) (s : ℝ) {ε R χ D R' : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hdepth0 : depth 0 = s)
    (hB : BlocksAt cfg k s R') (hb : Measurable (cfg.b k))
    (hπ : MeasureTheory.IsProbabilityMeasure (cfg.π k)) (hρμ : L.ρs ≤ cfg.μ k)
    [IsFiniteMeasure L.ρs]
    {m K₁ Mst r v' Rc s₁ ζ Lv Xb B δ A w : ℝ} (KB : Finset (Fin 3 → ℤ))
    (hχv : χ = cfg.N k ^ (-v')) (hN : 0 < cfg.N k)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' v')
    (hnum : ∀ jj : Fin (2 ^ cfg.T k s), ∀ κ ∈ KB,
      KeyNum (cfg.N k) (cfg.K k) cfg.d r v' Rc s₁ (slotStart cfg k s jj) (slotLen cfg k s) m ζ Lv
        (cfg.N k ^ (-s)) Xb K₁ B
        (cfg.K k + 12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
          (2 * χ + slotLen cfg k s * (ζ + χ)) / cfg.N k ^ (-s))
        ((cfg.N k ^ ε * cfg.N k ^ (-depth 0) +
          7 * (160 * cfg.N k ^ ε) * (slotLen cfg k s * (ζ + χ)) / (4 * D)) / cfg.N k ^ (-s))
        δ Mst A w η R₀ κ)
    (hKBb : ∀ κ ∈ KB, |(κ 0 : ℝ) * χ| ≤ Lv ∧ |(κ 1 : ℝ) * χ| ≤ Lv ∧ |(κ 2 : ℝ) * m| ≤ Lv)
    (hnull : L.ρs (horizSet (cfg.b k) ζ)ᶜ = 0)
    (hχ : 0 < χ) (hD : 0 < D) (hm : 0 < m) (hK1 : 1 ≤ cfg.K k)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hXb1 : 1 ≤ Xb) (hKa : cfg.K k * cfg.N k ^ (-s) ≤ 1)
    (hdrift : ζ + χ ≤ D / 4) (hsmallD : 4 * m + slotLen cfg k s * (ζ + χ) ≤ 4 * D)
    (hBblk : 8 * (12 * Xb ^ 2 * (cfg.K k * (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
      (2 + 4 * Lv + 3 * m) / cfg.N k ^ (-s)) ≤ B)
    (hBsh : 8 * (11 * (160 * cfg.N k ^ ε) / cfg.N k ^ (-s)) ≤ B) :
    L.ρs (shortBad cfg k s L m K₁ Mst KB) ≤
      ENNReal.ofReal (blockSum cfg k s L m KB / K₁) +
        ∑ h : Fin 3, ENNReal.ofReal (pieceSum cfg k s L m KB h / K₁) +
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
          (blockSum cfg k s L m KB + pieceSum cfg k s L m KB 0)) := by
  classical
  rcases KB.eq_empty_or_nonempty with hKB | ⟨κ₀, hκ₀⟩
  · subst hKB
    have hempty : shortBad cfg k s L m K₁ Mst (∅ : Finset (Fin 3 → ℤ)) = ∅ := by
      simp [shortBad]
    rw [hempty, measure_empty]
    exact zero_le
  have hn0 := hnum ⟨0, pow_pos (by norm_num) _⟩ κ₀ hκ₀
  have hK₁ : 0 < K₁ := hn0.hK₁
  have hMst : 0 < Mst := lt_of_lt_of_le hn0.hW₁ hn0.hW₁M
  have hδ : 0 < δ := by linarith [hn0.hW₁, hn0.hW₂, hn0.hδW]
  have hA1 : 1 ≤ A := hn0.hA1
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  have hT : ∀ κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ :=
    fun κ => shortBound_keyRef_nonneg cfg k hχ.le hm.le hq0.le ha.le κ
  have hTh : ∀ h κ, 0 ≤ keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-depth h)) κ :=
    fun h κ => shortBound_keyRef_nonneg cfg k hχ.le hm.le hq0.le
      (Real.rpow_pos_of_pos hN _).le κ
  have hX : 0 ≤ A * (Mst / δ) ^ (-η) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (div_pos hMst hδ).le _)
  have hterm : ∀ (jj : Fin (2 ^ cfg.T k s)) (κ : Fin 3 → ℤ), 0 ≤ A * (Mst / δ) ^ (-η) *
      ((Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) +
        Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
        keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) :=
    fun jj κ => mul_nonneg hX (mul_nonneg (by positivity) (hT κ))
  unfold shortBad
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (shortBound_light_blocks_le cfg k s L m K₁ KB hK₁.le hT)
      (shortBound_light_pieces_le cfg k s L m K₁ KB hK₁.le hTh))) ?_)
  refine (shortBound_pairs_le cfg k s L m K₁ Mst KB).trans ?_
  calc _ ≤ ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
        ((Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) +
          Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ)) :=
        Finset.sum_le_sum fun jj _ => Finset.sum_le_sum fun κ hκ =>
          shortBound_key_le cfg hPC k s L hdepth0 hB hb hπ hρμ hχv hN hcap jj κ
            (hnum jj κ hκ) (hKBb κ hκ) hnull hχ hD hm hK1 hXb hXb1 hKa hdrift hsmallD hBblk
            hBsh
    _ = ENNReal.ofReal (∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, A * (Mst / δ) ^ (-η) *
        ((Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) +
          Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
          keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun jj _ => Finset.sum_nonneg fun κ _ => hterm jj κ)]
        refine Finset.sum_congr rfl fun jj _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun κ _ => hterm jj κ)]
    _ ≤ ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
        (blockSum cfg k s L m KB + pieceSum cfg k s L m KB 0)) := by
        apply ENNReal.ofReal_le_ofReal
        have hb1 := shortBound_block_count_le cfg k s L m K₁ KB hT
        have hp1 := shortBound_piece_count_le cfg k s L hdepth0 m K₁ KB hT
        have e : ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB, A * (Mst / δ) ^ (-η) *
            ((Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) +
              Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
              keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) =
            A * (Mst / δ) ^ (-η) * (∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
              (Fintype.card (ShortHeavyBlocks cfg k s L m K₁ jj κ) : ℝ) *
                keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ +
              ∑ jj : Fin (2 ^ cfg.T k s), ∑ κ ∈ KB,
              (Fintype.card (ShortHeavyPieces cfg k s L m K₁ jj κ) : ℝ) *
                keyRef cfg k χ m (slotLen cfg k s) (cfg.N k ^ (-s)) κ) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun jj _ => ?_
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun κ _ => ?_
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (add_le_add hb1 hp1) hX

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
