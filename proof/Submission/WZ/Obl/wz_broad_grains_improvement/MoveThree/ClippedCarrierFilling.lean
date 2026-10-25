-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedCarrierFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedPacketMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedPacketFilling

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)
open WangZahlLot.Obl.wz_broad_grains_initialization (packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

noncomputable section
namespace ClippedCarrierAngularData

variable {σ ω ζ δ ε b ρ c β τ den k Cnet e u t loss density β₂ q₀ jump τ₂ : ℝ}
  {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
  {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
  {l : Fin A.labels.card} {j : Fin (N.N l)}
  {B : PhysicalCarrierBox N loss density l j} {hδ : 0 < δ}

def start (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) (i : Fin R.card) : V :=
  B.map hδ (D.z (enumerate R i)) - (1 / 2 : ℝ) • B.direction hδ i

abbrev labels (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) :=
  packetLabelUniverse Q.scale Q.start (B.direction hδ)

def normalizedPiece (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (a : Q.labels) (i : Fin R.card) : Set V :=
  packetPiece Q.scale (B.direction hδ) (fun i => B.map hδ '' Q.shade i)
    (fun p => Q.packets ((B.map hδ).symm p))
    (fun p W => Q.center ((B.map hδ).symm p) W) a i

def packetShort (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) : ℝ :=
  min (36 * B.slabWidth) (min (80 * Q.scale) 4)

def packetMiddle (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂) : ℝ :=
  min (80 * Q.scale) 4

theorem input_mem_fibre (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (i : Fin R.card) (hi : (Q.input i ∩ Q.cut).Nonempty) :
    i ∈ N.fibre l j := by
  by_contra hh
  obtain ⟨q, hq⟩ := hi
  have hqi := Q.input_subset i hq.1
  rw [N.physicalPiece_outside l j i hh] at hqi
  exact hqi

/-- All labels of one actual high carrier receive filled normalized prisms.
Whole original grains, the old-grain index and the actual normalized
packet shading are retained in the output. -/
structure Filling (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (rowExp fillExp : ℝ) where
  center : Q.labels → V
  frame : Q.labels → V ≃ₗᵢ[ℝ] V
  shade : Q.labels → Fin R.card → Set V
  whole : ∀ a i, (Q.normalizedPiece a i).Nonempty →
    B.map hδ '' P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i)) ⊆
      P Q.packetShort Q.packetMiddle 4 (center a) (frame a)
  measurable : ∀ a i, MeasurableSet (shade a i)
  subset : ∀ a i, shade a i ⊆ Q.normalizedPiece a i
  contained : ∀ a i, shade a i ⊆ P Q.packetShort Q.packetMiddle 4 (center a) (frame a)
  mass : (1 / 2 : ENNReal) * (∑ i, μ (B.map hδ '' Q.shade i)) ≤
    ∑ a, ∑ i, μ (shade a i)
  row_mass : ∀ a i, (shade a i).Nonempty → O (δ ^ rowExp * (2 * ρ) ^ 2) ≤ μ (shade a i)
  counts : ∀ a p, p ∈ ⋃ i, shade a i →
    q R.card {i | p ∈ Q.normalizedPiece a i} ≤ 4 * q R.card {i | p ∈ shade a i}
  broad : ∀ a p u' r, 2 * ρ ≤ r →
    q R.card {i | p ∈ shade a i ∧ pd (B.direction hδ i) u' ≤ r} ≤
      8 * (r / Q.scale) ^ β₂ * q R.card {i | p ∈ shade a i}
  dense : ∀ a, (⋃ i, shade a i).Nonempty →
    O (δ ^ fillExp) * μ (P Q.packetShort Q.packetMiddle 4 (center a) (frame a)) ≤
      μ (⋃ i, shade a i)

end ClippedCarrierAngularData

theorem clipped_carrier_packet_fillings_uniform {β₂ jump' s h rowExp fillExp loss : ℝ}
    (hβ : 0 < β₂) (hs : 0 < s) (hsjump : s ≤ jump') (hh : h < rowExp)
    (hloss : 0 ≤ loss) (hgap : 3 * rowExp + s + loss < fillExp) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ ω ζ ε b ρ c β τ den k Cnet e u t density q₀ jump τ₂ : ℝ}
        {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
        {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
        {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
        {A : BlockAngularData D R G β τ} {hk : 0 < k}
        {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
        {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
        {l : Fin A.labels.card} {j : Fin (N.N l)}
        (B : PhysicalCarrierBox N loss density l j)
        (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂),
      l ∈ F.good → 2 * ρ ≤ 1 / 100 → B.slabWidth ≤ 1 / 8 →
      δ ^ (-jump') * (2 * ρ) ≤ Q.scale →
      δ ^ h ≤ (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) →
      Nonempty (Q.Filling rowExp fillExp) := by
  obtain ⟨d₀, hd₀, hd₀1, Hfill⟩ := normalized_packet_fillings hβ hs hsjump hh hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδ0 σ ω ζ ε b ρ c β τ den k Cnet e u t density q₀ jump τ₂
    p n d x v Y D R G A hk F N l j B Q hl hρsmall hslab hgrow hbudget
  have hδ1 : δ ≤ 1 := (hδ0.trans hd₀1).trans (by norm_num)
  have hδρ : δ ≤ 2 * ρ := by
    have hρ := (D.dimensions hδ).2.1
    have haρ := D.grains.2.1
    have hc1 := (D.dimensions hδ).2.2.2.2
    have hδa := D.grains.1
    nlinarith
  let Body := fun i : Fin R.card =>
    P D.a (ρ * c) c (D.z (enumerate R i)) (D.e (enumerate R i))
  have hinput (i : Fin R.card) : Q.input i ∩ Q.cut ⊆ Body i :=
    inter_subset_left.trans ((Q.input_subset i).trans ((N.physicalPiece_subset l j i).trans
      (D.grains.2.2.2.2.1 (enumerate R i)).2.1))
  have hgeom (i : Fin R.card) (hi : (Q.input i ∩ Q.cut).Nonempty) :=
    B.whole_ball_slab hδ hl hslab i (Q.input_mem_fibre i hi)
  obtain ⟨z, frame, W, hwhole, hW, hWbox, hmass, hrows, hcounts, hbroad, hdense⟩ :=
    Hfill δ (2 * ρ) Q.scale B.slabWidth hδ hδ0 hδρ hρsmall hgrow Q.upper
      (B.slabWidth_pos hδ) hslab (B.slabWidth_bound hδ hδ1 hloss)
      R.card Q.start (B.direction hδ) Body (fun i => Q.input i ∩ Q.cut)
      Q.shade Q.packets Q.center Q.refinement (B.direction_norm hδ) hinput (B.map hδ)
      (fun i hi => B.whole_tube hδ hl i (Q.input_mem_fibre i hi))
      (fun i hi => (hgeom i hi).trans inter_subset_left)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0) 0 (by simp)
      (fun i hi => by simpa only [EuclideanSpace.basisFun_inner, sub_zero] using
        (hgeom i hi).trans inter_subset_right)
      (fun i hi => by simpa only [EuclideanSpace.basisFun_inner] using
        B.direction_slab hδ hl i (Q.input_mem_fibre i hi))
      (N.fibre l j) Q.shade_outside (Q.normalized_mass_power hl hbudget)
  refine ⟨{
    center := z
    frame := frame
    shade := W
    whole := ?_
    measurable := fun a i => (hW a i).1
    subset := fun a i => (hW a i).2
    contained := hWbox
    mass := hmass
    row_mass := hrows
    counts := hcounts
    broad := hbroad
    dense := hdense
  }⟩
  intro a i hi
  apply hwhole a i
  obtain ⟨q, hq⟩ := hi
  exact ⟨(B.map hδ).symm q, by
    simpa only [affinePacketPiece, ClippedCarrierAngularData.normalizedPiece,
      mem_preimage, AffineEquiv.apply_symm_apply] using hq⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
