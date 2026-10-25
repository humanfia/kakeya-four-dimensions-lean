-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockWindowRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockWindowRows.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketWidth
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedWindowFilling
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

noncomputable section

structure CarrierWindowRows {σ ω ζ δ ε b ρ c β τ den k Cnet e u t loss density β₂ q₀ jump τ₂ : ℝ}
    {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    {A : BlockAngularData D R G β τ} {hk : 0 < k}
    {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
    {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
    {l : Fin A.labels.card} {j : Fin (N.N l)}
    {B : PhysicalCarrierBox N loss density l j} {hδ : 0 < δ}
    (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) (widthJump fillExp : ℝ) where
  count : ℕ
  short : Fin count → ℝ
  middle : Fin count → ℝ
  center : Fin count → V
  frame : Fin count → V ≃ₗᵢ[ℝ] V
  shade : Fin count → Fin R.card → Set V
  dimensions : ∀ k, (⋃ i, shade k i).Nonempty →
    δ ≤ short k ∧ short k ≤ middle k ∧ middle k ≤ c ∧
      δ ^ (-widthJump) * ρ * c ≤ middle k ∧ middle k ≤ 10737418240 * Q.scale * c
  measurable : ∀ k i, MeasurableSet (shade k i)
  subset : ∀ k i, shade k i ⊆ Q.shade i
  contained : ∀ k i, shade k i ⊆ P (short k) (middle k) c (center k) (frame k)
  disjoint : ∀ i, Pairwise fun k k' => Disjoint (shade k i) (shade k' i)
  mass : (1 / 34 : ENNReal) * (∑ i, μ (Q.shade i)) ≤ ∑ k, ∑ i, μ (shade k i)
  dense : ∀ k, (⋃ i, shade k i).Nonempty →
    O (δ ^ fillExp) * μ (P (short k) (middle k) c (center k) (frame k)) ≤ μ (⋃ i, shade k i)
  crosses : ∀ i ∈ D.S, ∀ k i', D.f i = D.γ (enumerate R i') →
    (D.Z i ∩ shade k i').Nonempty → Crosses δ (short k) (middle k) c (x i) (v i) (center k) (frame k)
  axis_close : ∀ k i, (shade k i).Nonempty →
    pd (B.direction hδ i) (B.frame (boxAxis (D.e (enumerate R i)) 2)) ≤ 2 * ρ
  broad : ∀ k p u' r, 2 * ρ ≤ r →
    q R.card {i | p ∈ shade k i ∧ pd (B.direction hδ i) u' ≤ r} ≤
      8 * (r / Q.scale) ^ β₂ * q R.card {i | p ∈ shade k i}

/-- Actual clipped carriers yield the physical, growing, fixed-length
window rows needed for incidence assembly. Old grain labels are injected
into the full witness only where the crossing and coarse count use them. -/
theorem block_window_rows_uniform {β₂ q₀ widthJump jump' s h rowExp fillExp loss : ℝ}
    (hβ : 0 < β₂) (hwidthJump : 0 < widthJump) (hwidthGap : β₂ + 3 * widthJump < q₀)
    (hs : 0 < s) (hst : s ≤ jump') (hhu : h < rowExp)
    (hloss : 0 ≤ loss) (hfill : 3 * rowExp + s + loss < fillExp) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ω ζ ε b ρ c β τ den k Cnet e u t density jump τ₂ : ℝ}
        {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
        {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
        {l : Fin A.labels.card} {j : Fin (N.N l)}
        {B : PhysicalCarrierBox N loss density l j}
        (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂),
      l ∈ F.good → (∀ i, ‖v i‖ = 1) → (∀ i, D.Z i ⊆ T δ (x i) (v i)) →
      (∀ i, Disjoint (D.Z i) (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ c (x i) (v i))) →
      2 * ρ ≤ 1 / 100 → B.slabWidth ≤ 1 / 8 →
      δ ^ (-jump') * (2 * ρ) ≤ Q.scale → Q.scale ≤ 1 / 2 ^ 35 →
      δ ^ h ≤ (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) →
      Nonempty (CarrierWindowRows Q widthJump fillExp) := by
  classical
  obtain ⟨dF, hdF, hdF1, HF⟩ := clipped_packet_window_fillings hβ hs hst hhu hfill
  obtain ⟨dW, hdW, hdW1, HW⟩ := block_clipped_packet_width_uniform hβ.le hwidthJump hwidthGap
  refine ⟨min dF dW, lt_min hdF hdW, (min_le_left _ _).trans hdF1, ?_⟩
  intro δ hδ hδ0 σ ω ζ ε b ρ c β τ den k Cnet e u t density jump τ₂
    p n d x v Y D R G A hk F N l j B Q hl hv hZT hclear hρsmall hslab hgrow hmax hbudget
  have hδF := hδ0.trans (min_le_left _ _)
  have hδW := hδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := (hδF.trans hdF1).trans (by norm_num)
  obtain ⟨ha, hρ, hρ1, hc, _⟩ := D.dimensions hδ
  have hδρ : δ ≤ 2 * ρ := by
    nlinarith only [hρ, D.grains.1, D.grains.2.1, (D.dimensions hδ).2.2.2.2]
  have hδc : 16 * δ ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hρsmall hc.le
    nlinarith only [hh, hc, D.grains.1, D.grains.2.1]
  have hYBody (i : Fin R.card) : Q.input i ∩ Q.cut ⊆
      P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) :=
    inter_subset_left.trans ((Q.input_subset i).trans ((N.physicalPiece_subset l j i).trans
      (D.grains.2.2.2.2.1 (enumerate R i)).2.1))
  obtain ⟨a, b', z, frame, W, hdim, haA, hwhole, hW, hdisj, hkeep, hrows, haxis, hdense⟩ :=
    HF δ ρ Q.scale D.a c B.short B.middle (8 * c) hδ hδF hδρ hρsmall hgrow hmax
      ha hρ hc (B.short_pos hδ) D.grains.2.1 hslab (B.slabWidth_bound hδ hδ1 hloss)
      R.card (fun i => D.z (enumerate R i)) (fun i => D.e (enumerate R i))
      (D.z G.natural_anchor) B.center B.frame (fun i => Q.input i ∩ Q.cut)
      Q.shade Q.packets Q.center Q.refinement hYBody
      (fun i hi => B.whole_body hδ hl i (Q.input_mem_fibre i hi))
      (N.fibre l j) Q.shade_outside (Q.normalized_mass_power hl hbudget)
  let κ := Q.labels × Fin 6145
  let zWin : κ → V := fun k => axialWindowCenter c (384 * c) (z k.1) (frame k.1) k.2
  have hWZ (k : κ) (i : Fin R.card) : W k i ⊆ Q.shade i :=
    ((hW k i).2.trans inter_subset_left).trans
      (affinePacketPiece_subset (B.map hδ) Q.scale (B.direction hδ) Q.shade Q.packets Q.center k.1 i)
  have hWH (k : κ) (i : Fin R.card) : W k i ⊆ D.Hg (enumerate R i) :=
    (hWZ k i).trans (((Q.refinement.1 i).2.trans inter_subset_left).trans
      ((Q.input_subset i).trans (N.physicalPiece_subset l j i)))
  have hocc (k : κ) (hk : (⋃ i, W k i).Nonempty) :
      (⋃ i, affinePacketPiece (B.map hδ) Q.scale (B.direction hδ)
        Q.shade Q.packets Q.center k.1 i).Nonempty := by
    obtain ⟨i, hi⟩ := nonempty_iUnion.mp hk
    exact nonempty_iUnion.mpr ⟨i, hi.mono ((hW k i).2.trans inter_subset_left)⟩
  have hwidth (k : κ) (hk : (⋃ i, W k i).Nonempty) :
      D.a ≤ a k.1 ∧ a k.1 ≤ b' k.1 ∧ 128 * b' k.1 ≤ c :=
    ⟨haA k.1 (hocc k hk), (hdim k.1).2.1, (hdim k.1).2.2.1⟩
  have hcross (i : Fin n) (hi : i ∈ D.S) (k : κ) (i' : Fin R.card)
      (hf : D.f i = D.γ (enumerate R i')) (hne : (D.Z i ∩ W k i').Nonempty) :
      Crosses δ (128 * a k.1) (128 * b' k.1) c (x i) (v i) (zWin k) (frame k.1) := by
    obtain ⟨q, hqZ, hqW⟩ := hne
    have hWne : (W k i').Nonempty := ⟨q, hqW⟩
    obtain ⟨haA', hab, hbc⟩ := hwidth k (nonempty_iUnion.mpr ⟨i', hWne⟩)
    have hends := (D.grains.2.2.2.2.2.2.2.2.2.1 i hi (enumerate R i') hf
      ⟨q, hqZ, hWH k i' hqW⟩).2.2
    apply wider_prism_crossing_of_contained_grain (D.e (enumerate R i')) (frame k.1)
      hδ (D.grains.1.trans haA') hab hδc hbc (hv i)
      (hwhole k.1 i' (hWne.mono ((hW k i').2.trans inter_subset_left))) hends
    have hcore := ((hW k i').2 hqW).2
    refine ⟨⟨hZT i hqZ, fun hp => Set.disjoint_left.mp (hclear i) hqZ hp⟩,
      hcore.1.trans ?_, hcore.2.1.trans ?_, hcore.2.2⟩ <;>
      linarith only [(hdim k.1).1, (hdim k.1).1.trans hab]
  let idx : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨{
    count := Fintype.card κ
    short := fun k => 128 * a (idx k).1
    middle := fun k => 128 * b' (idx k).1
    center := fun k => zWin (idx k)
    frame := fun k => frame (idx k).1
    shade := fun k => W (idx k)
    dimensions := ?_
    measurable := fun k i => (hW (idx k) i).1
    subset := fun k => hWZ (idx k)
    contained := ?_
    disjoint := fun i k k' hne => hdisj i (idx.injective.ne hne)
    mass := hkeep.trans_eq (Equiv.sum_comp idx (fun k => ∑ i, μ (W k i))).symm
    dense := fun k => hdense (idx k)
    crosses := fun i hi k => hcross i hi (idx k)
    axis_close := ?_
    broad := fun k => haxis (idx k)
  }⟩
  · intro k hk
    obtain ⟨haA', hab, hbc⟩ := hwidth (idx k) hk
    have hw := HW δ hδ hδW Q (a (idx k).1) (b' (idx k).1) (384 * c)
      (z (idx k).1) (frame (idx k).1) (idx k).1 (hdim (idx k).1).1 hab
      (hwhole (idx k).1) (hocc (idx k) hk)
    have hbup := (hdim (idx k).1).2.2.2
    refine ⟨?_, ?_, hbc, ?_, ?_⟩ <;>
      nlinarith only [hδ, D.grains.1, haA', hab, hw, hbup]
  · intro k i q hq
    have hcore := ((hW (idx k) i).2 hq).2
    refine ⟨hcore.1.trans ?_, hcore.2.1.trans ?_, hcore.2.2.trans ?_⟩ <;>
      linarith only [hc, (hdim (idx k).1).1, (hdim (idx k).1).1.trans (hdim (idx k).1).2.1]
  · intro k i hi
    have hinput := (hi.mono (hWZ (idx k) i)).mono (Q.refinement.1 i).2
    exact (min_le_left _ _).trans (B.linear_data hδ hl i (Q.input_mem_fibre i hinput)).2

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
