-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyDyadic
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (PhysicalPacket AffineCell prism slab quantitative_affine_normalization
    exists_large_color_class)

/-- Source geometry used throughout the refinement. -/
structure BodyGeometry {n : ℕ} (U : Fin n → Set Space) (x : Fin n → Space)
    (δ B w : ℝ) : Prop where
  compact : ∀ i, IsCompact (U i)
  convex : ∀ i, Convex ℝ (U i)
  bounded : ∀ i, U i ⊆ closedBall (0 : Space) 1
  interior : ∀ i, ball (x i) δ ⊆ U i
  diameter : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 16 : ℝ) ≤ dist p q
  width : ∀ i, WideSection (U i) B
  volume_bounds : ∀ i, ENNReal.ofReal w ≤ volume (U i) ∧
    volume (U i) ≤ ENNReal.ofReal (384 * w)

structure BodyPacketValid {n : ℕ} (U Y : Fin n → Set Space) (d : ℝ)
    (C : PhysicalPacket n) : Prop where
  nonempty : C.indices.Nonempty
  compact : IsCompact C.region
  convex : Convex ℝ C.region
  bounded : C.region ⊆ closedBall (0 : Space) 1
  whole : ∀ i ∈ C.indices, U i ⊆ C.region
  measurable : ∀ i ∈ C.indices, MeasurableSet (C.shading i)
  original : ∀ i ∈ C.indices, C.shading i ⊆ Y i
  source : ∀ i ∈ C.indices, C.shading i ⊆ U i
  density : ∀ i ∈ C.indices, ENNReal.ofReal d * volume (U i) ≤ volume (C.shading i)

structure BodyCellValid {n K : ℕ} (U Y : Fin n → Set Space) (B h : ℝ)
    (G : AffineCell n K) : Prop where
  nonempty : G.indices.Nonempty
  ordered : G.a ≤ G.b
  small : G.b ≤ 1 / 1000000
  width : B * h / 2 ≤ G.b
  jacobian_pos : 0 < G.jacobian
  volume_identity : ∀ Q : Set Space,
    volume (G.affine '' Q) = ENNReal.ofReal G.jacobian * volume Q
  body_small : ∀ i ∈ G.indices, G.body i ⊆ ball (0 : Space) (1 / 100)
  whole : ∀ i ∈ G.indices, U i ⊆ G.affine '' G.body i
  measurable : ∀ i ∈ G.indices, MeasurableSet (G.shading i)
  shading : ∀ i ∈ G.indices, G.shading i ⊆ G.body i ∩ G.affine ⁻¹' Y i
  density : ∀ i ∈ G.indices, ENNReal.ofReal h * volume (G.body i) ≤ volume (G.shading i)
  regular : ∀ i ∈ G.indices, ∀ p ∈ G.shading i, ∀ r : ℝ, G.a ≤ r → r ≤ 1 →
    ENNReal.ofReal h * volume (G.body i ∩ ball p r) ≤ volume (G.shading i ∩ ball p r)
  transverse : ∀ p, (∃ i ∈ G.indices, p ∈ G.shading i) →
    ∃ i ∈ G.indices, ∃ j ∈ G.indices, p ∈ G.shading i ∧ p ∈ G.shading j ∧
      h ≤ G.a / G.b + min ‖G.axes i 0 - G.axes j 0‖ ‖G.axes i 0 + G.axes j 0‖
  slabs : ∀ (ν : Space) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ G.indices ∧
      G.body i ⊆ ball (0 : Space) 1 ∩ slab (innerSL ℝ ν) s r} : ℝ) ≤
    ENNReal.ofReal (h⁻¹ * (G.indices.card : ℝ)) *
      volume (ball (0 : Space) 1 ∩ slab (innerSL ℝ ν) s r)

structure BodyPrepared {n K : ℕ} (U : Fin n → Set Space)
    (C : PhysicalPacket n) (δ B S : ℝ) where
  cell : AffineCell n K
  nonempty : cell.indices.Nonempty
  indices : cell.indices ⊆ C.indices
  retained : (C.indices.card : ℝ) ≤ (K + 1 : ℕ) ^ 2 * (cell.indices.card : ℝ)
  jacobian_pos : 0 < cell.jacobian
  small : cell.affine ⁻¹' C.region ⊆ closedBall (0 : Space) (2 / S)
  lipschitz : ∀ p q, dist (cell.affine p) (cell.affine q) ≤ (6 * S) * dist p q
  volume_identity : ∀ Q : Set Space,
    volume (cell.affine '' Q) = ENNReal.ofReal cell.jacobian * volume Q
  jacobian_volume : ENNReal.ofReal cell.jacobian ≤
    ENNReal.ofReal (64 * S ^ 3) * volume C.region
  short_lower : δ / (12 * S) ≤ cell.a
  middle_lower : B / (24 * S) ≤ cell.b
  ordered : cell.a ≤ cell.b
  short_small : cell.b ≤ 1 / 1000000
  body_small : ∀ i ∈ cell.indices, cell.body i ⊆ ball (0 : Space) (1 / 100)
  whole : ∀ i ∈ cell.indices, U i ⊆ cell.affine '' cell.body i
  body_volume : ∀ i ∈ cell.indices, volume (cell.body i) ≤
    ENNReal.ofReal (400000 * S) * volume (cell.affine ⁻¹' U i)
  shading_eq : ∀ i, cell.shading i = cell.affine ⁻¹' C.shading i

theorem prepare_bodies {n K : ℕ} {U Y : Fin n → Set Space} {x : Fin n → Space}
    {δ B w d S : ℝ} (F : BodyGeometry U x δ B w)
    {C : PhysicalPacket n} (P : BodyPacketValid U Y d C)
    (hδ : 0 < δ) (hS : 1000000000 ≤ S)
    (hK : (1 / 2 : ℝ) ^ K < δ / (6 * S)) :
    Nonempty (BodyPrepared (K := K) U C δ B S) := by
  classical
  obtain ⟨i₀, hi₀⟩ := P.nonempty
  obtain ⟨f, D, hD, _, hfsmall, hfLip, hfvol, hDvol, _⟩ :=
    quantitative_affine_normalization P.compact P.convex hδ (by linarith : 0 < S)
      ((F.interior i₀).trans (P.whole i₀ hi₀)) P.bounded
  have choices : ∀ i : Fin n, ∃ (k l : Fin (K + 1))
      (u : OrthonormalBasis (Fin 3) ℝ Space), i ∈ C.indices →
      δ / (12 * S) ≤ (1 / 2 : ℝ) ^ k.val ∧
      (1 / 2 : ℝ) ^ k.val ≤ (1 / 2 : ℝ) ^ l.val ∧
      B / (24 * S) ≤ (1 / 2 : ℝ) ^ l.val ∧
      (1 / 2 : ℝ) ^ l.val ≤ 48 / S ∧ (1 / 2 : ℝ) ^ l.val ≤ 1 / 1000000 ∧
      prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u ⊆
        ball (0 : Space) (1 / 100) ∧
      U i ⊆ f '' prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u ∧
      volume (prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u) ≤
        ENNReal.ofReal (400000 * S) * volume (f ⁻¹' U i) := by
    intro i
    by_cases hi : i ∈ C.indices
    · obtain ⟨k, l, u, H⟩ := normalized_dyadic_body (F.compact i) (F.convex i)
        hδ hS hK (F.interior i) (F.diameter i) (F.width i) f
        ((preimage_mono (P.whole i hi)).trans hfsmall) hfLip
      exact ⟨k, l, u, fun _ => H⟩
    · exact ⟨0, 0, EuclideanSpace.basisFun (Fin 3) ℝ, fun h => (hi h).elim⟩
  choose k l u H using choices
  obtain ⟨kl, hnonempty, hcard⟩ :=
    exists_large_color_class C.indices P.nonempty (fun i => (k i, l i))
  let J := C.indices.filter fun i => (k i, l i) = kl
  let G : AffineCell n K := {
    indices := J, first := kl.1, second := kl.2, affine := f, jacobian := D,
    center := fun i => f.symm (x i), axes := u, shading := fun i => f ⁻¹' C.shading i }
  have hJ : J.Nonempty := hnonempty
  have hJC : J ⊆ C.indices := Finset.filter_subset _ _
  have hG (i : Fin n) (hi : i ∈ J) :
      δ / (12 * S) ≤ G.a ∧ G.a ≤ G.b ∧ B / (24 * S) ≤ G.b ∧
      G.b ≤ 48 / S ∧ G.b ≤ 1 / 1000000 ∧ G.body i ⊆ ball (0 : Space) (1 / 100) ∧
      U i ⊆ f '' G.body i ∧
      volume (G.body i) ≤ ENNReal.ofReal (400000 * S) * volume (f ⁻¹' U i) := by
    obtain ⟨hk, hl⟩ := Prod.mk.inj (Finset.mem_filter.mp hi).2
    have hh := H i (hJC hi)
    simpa only [hk, hl, AffineCell.a, AffineCell.b, AffineCell.body, G] using hh
  obtain ⟨j, hj⟩ := hJ
  refine ⟨{
    cell := G, nonempty := ⟨j, hj⟩, indices := hJC, retained := ?_,
    jacobian_pos := hD, small := hfsmall, lipschitz := hfLip,
    volume_identity := hfvol, jacobian_volume := hDvol,
    short_lower := (hG j hj).1, middle_lower := (hG j hj).2.2.1,
    ordered := (hG j hj).2.1, short_small := (hG j hj).2.2.2.2.1,
    body_small := fun i hi => (hG i hi).2.2.2.2.2.1,
    whole := fun i hi => (hG i hi).2.2.2.2.2.2.1,
    body_volume := fun i hi => (hG i hi).2.2.2.2.2.2.2,
    shading_eq := fun _ => rfl }⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two, G, J] using hcard

theorem BodyPrepared.preimage_body {n K : ℕ} {U : Fin n → Set Space}
    {C : PhysicalPacket n} {δ B S : ℝ} (A : BodyPrepared (K := K) U C δ B S)
    {i : Fin n} (hi : i ∈ A.cell.indices) : A.cell.affine ⁻¹' U i ⊆ A.cell.body i := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := A.whole i hi hp
  exact A.cell.affine.injective heq ▸ hq

end WangZahlLot.Obl.wz_flat_factored_improvement
