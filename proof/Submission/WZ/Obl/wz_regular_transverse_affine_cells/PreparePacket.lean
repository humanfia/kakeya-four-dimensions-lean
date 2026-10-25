-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PreparePacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

structure PreparedPacket {n K : ℕ} (C : PhysicalPacket n) (δ S : ℝ) (x v : Fin n → E) where
  cell : AffineCell n K
  nonempty : cell.indices.Nonempty
  indices_subset : cell.indices ⊆ C.indices
  retained : (C.indices.card : ℝ) ≤ (K + 1 : ℕ) ^ 2 * (cell.indices.card : ℝ)
  jacobian_pos : 0 < cell.jacobian
  small : cell.affine ⁻¹' C.region ⊆ closedBall (0 : E) (2 / S)
  lipschitz : ∀ p q, dist (cell.affine p) (cell.affine q) ≤ (6 * S) * dist p q
  volume_identity : ∀ Q : Set E, volume (cell.affine '' Q) = ENNReal.ofReal cell.jacobian * volume Q
  jacobian_volume : ENNReal.ofReal cell.jacobian ≤ ENNReal.ofReal (64 * S ^ 3) * volume C.region
  jacobian_lower : δ ^ 3 ≤ cell.jacobian * (2 / S) ^ 3
  short_lower : δ / (12 * S) ≤ cell.a
  ordered : cell.a ≤ cell.b
  short_upper : cell.b ≤ 48 / S
  short_small : cell.b ≤ 1 / 1000000
  body_small : ∀ i ∈ cell.indices, cell.body i ⊆ ball (0 : E) (1 / 100)
  whole_body : ∀ i ∈ cell.indices, closedTube δ (x i) (v i) ⊆ cell.affine '' cell.body i
  body_volume : ∀ i ∈ cell.indices, volume (cell.body i) ≤ ENNReal.ofReal (400000 * S) *
    volume (cell.affine ⁻¹' closedTube δ (x i) (v i))
  shading_eq : ∀ i, cell.shading i = cell.affine ⁻¹' C.shading i

lemma prepare_packet {n K : ℕ} {C : PhysicalPacket n} {δ d S : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y)
    (hδ : 0 < δ) (hSlarge : 1000000000 ≤ S)
    (hK : (1 / 2 : ℝ) ^ K < δ / (6 * S))
    (hv : ∀ i, ‖v i‖ = 1) (htube : ∀ i, tube δ (x i) (v i) ⊆ ball (0 : E) 1) :
    Nonempty (PreparedPacket (K := K) C δ S x v) := by
  classical
  obtain ⟨hI, hcompact, hconv, hbound, hwhole, hYm, hYsub, hYbody, hdense⟩ := hC
  have hIcopy := hI
  obtain ⟨i₀, hi₀⟩ := hIcopy
  have hS : 0 < S := by linarith
  have hball : ball (x i₀) δ ⊆ C.region :=
    ((ball_subset_tube (x i₀) (v i₀)).trans (tube_subset_closedTube _ _ _)).trans (hwhole i₀ hi₀)
  obtain ⟨f, D, hD, hf0, hfsmall, hfLip, hfvol, hDvol, hDlow⟩ :=
    quantitative_affine_normalization hcompact hconv hδ hS hball hbound
  have hsmall : ∀ i ∈ C.indices, f ⁻¹' closedTube δ (x i) (v i) ⊆ closedBall (0 : E) (2 / S) :=
    fun i hi => (preimage_mono (hwhole i hi)).trans hfsmall
  have hchoices : ∀ i : Fin n, ∃ (k l : Fin (K + 1)) (u : OrthonormalBasis (Fin 3) ℝ E),
      i ∈ C.indices →
      δ / (12 * S) ≤ (1 / 2 : ℝ) ^ k.val ∧ (1 / 2 : ℝ) ^ k.val ≤ (1 / 2 : ℝ) ^ l.val ∧
      (1 / 2 : ℝ) ^ l.val ≤ 48 / S ∧ (1 / 2 : ℝ) ^ l.val ≤ 1 / 1000000 ∧
      prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u ⊆ ball (0 : E) (1 / 100) ∧
      closedTube δ (x i) (v i) ⊆ f '' prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u ∧
      volume (prism ((1 / 2 : ℝ) ^ k.val) ((1 / 2 : ℝ) ^ l.val) (f.symm (x i)) u) ≤
        ENNReal.ofReal (400000 * S) * volume (f ⁻¹' closedTube δ (x i) (v i)) := by
    intro i
    by_cases hi : i ∈ C.indices
    · obtain ⟨k, l, u, hu⟩ := normalized_dyadic_tube_prism hδ hSlarge hK f (x i) (v i)
        (hv i) (htube i) (hsmall i hi) hfLip
      exact ⟨k, l, u, fun _ => hu⟩
    · exact ⟨0, 0, EuclideanSpace.basisFun (Fin 3) ℝ, fun h => False.elim (hi h)⟩
  choose k l u hu using hchoices
  obtain ⟨kl, hJ, hret⟩ := exists_large_color_class C.indices hI (fun i => (k i, l i))
  let J := C.indices.filter fun i => (k i, l i) = kl
  have hJI : J ⊆ C.indices := Finset.filter_subset _ _
  have hkl : ∀ i ∈ J, k i = kl.1 ∧ l i = kl.2 := by
    intro i hi
    exact Prod.mk.inj (Finset.mem_filter.mp hi).2
  let A : AffineCell n K := {
    indices := J, first := kl.1, second := kl.2, affine := f, jacobian := D,
    center := fun i => f.symm (x i), axes := u, shading := fun i => f ⁻¹' C.shading i }
  have hprops : ∀ i ∈ J,
      δ / (12 * S) ≤ A.a ∧ A.a ≤ A.b ∧ A.b ≤ 48 / S ∧ A.b ≤ 1 / 1000000 ∧
      A.body i ⊆ ball (0 : E) (1 / 100) ∧ closedTube δ (x i) (v i) ⊆ f '' A.body i ∧
      volume (A.body i) ≤ ENNReal.ofReal (400000 * S) * volume (f ⁻¹' closedTube δ (x i) (v i)) := by
    intro i hi
    obtain ⟨hk, hl⟩ := hkl i hi
    have h := hu i (hJI hi)
    rw [hk, hl] at h
    exact h
  have hJnonempty : J.Nonempty := by simpa only [J] using hJ
  obtain ⟨j₀, hj₀⟩ := hJnonempty
  obtain ⟨ha, hab, hb, hbsmall, _, _, _⟩ := hprops j₀ hj₀
  refine ⟨{
    cell := A, nonempty := ⟨j₀, hj₀⟩, indices_subset := hJI, retained := ?_,
    jacobian_pos := hD, small := hfsmall, lipschitz := hfLip, volume_identity := hfvol,
    jacobian_volume := hDvol, jacobian_lower := hDlow,
    short_lower := ha, ordered := hab, short_upper := hb, short_small := hbsmall,
    body_small := fun i hi => (hprops i hi).2.2.2.2.1,
    whole_body := fun i hi => (hprops i hi).2.2.2.2.2.1,
    body_volume := fun i hi => (hprops i hi).2.2.2.2.2.2, shading_eq := fun _ => rfl }⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two, A, J] using hret

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
