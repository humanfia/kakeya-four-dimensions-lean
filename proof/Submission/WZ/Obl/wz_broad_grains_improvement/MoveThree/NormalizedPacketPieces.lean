-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NormalizedPacketPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NormalizedPacketPieces.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CappedAngularPackets
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainPieces

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketLabel packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)
open WangZahlLot.Obl.wz_separated_cover_refinement
  (enumerate enumerate_mem enumerate_injective enumerate_sum)

noncomputable section
namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

def unitStart (A : BlockAngularData D R G β τ) (i : Fin R.card) : V :=
  A.start i + (1 / 2 : ℝ) • A.axis i - (1 / 2 : ℝ) • unit (A.axis i)

def labels (A : BlockAngularData D R G β τ) : Finset PacketLabel :=
  packetLabelUniverse A.scale A.unitStart (fun i => unit (A.axis i))

theorem axis_ne_zero (A : BlockAngularData D R G β τ) (i : Fin R.card) : A.axis i ≠ 0 := by
  intro he
  have hh := (A.lengths i).1
  rw [he, norm_zero] at hh
  norm_num at hh

theorem unit_axis_norm (A : BlockAngularData D R G β τ) (i : Fin R.card) :
    ‖unit (A.axis i)‖ = 1 := norm_unit (A.axis_ne_zero i)

theorem unit_body_tube (A : BlockAngularData D R G β τ) (i : Fin R.card) :
    D.normalizedBody R G.affine i ⊆ T (2 * ρ) (A.unitStart i) (unit (A.axis i)) :=
  (A.tubes i).trans (short_tube_unit_extension (A.start i) (A.axis i)
    (A.axis_ne_zero i) (A.lengths i).2)

/-- The actual angular packet pieces, pulled back and returned to the old
grain indexing. Grains outside this saturated block have empty pieces. -/
def grainPiece (A : BlockAngularData D R G β τ) (j : Fin D.L)
    (l : Fin A.labels.card) : Set V :=
  if hj : j ∈ R then G.affine ⁻¹'
    packetPiece A.scale (fun i => unit (A.axis i)) A.shade A.packets A.center
      (enumerate A.labels l) (R.equivFin ⟨j, hj⟩)
  else ∅

theorem grainPiece_enumerate (A : BlockAngularData D R G β τ)
    (i : Fin R.card) (l : Fin A.labels.card) :
    A.grainPiece (enumerate R i) l = G.affine ⁻¹'
      packetPiece A.scale (fun i => unit (A.axis i)) A.shade A.packets A.center
        (enumerate A.labels l) i := by
  simp [grainPiece, WangZahlLot.Obl.wz_separated_cover_refinement.enumerate]

theorem image_grainPiece (A : BlockAngularData D R G β τ)
    (i : Fin R.card) (l : Fin A.labels.card) :
    G.affine '' A.grainPiece (enumerate R i) l =
      packetPiece A.scale (fun i => unit (A.axis i)) A.shade A.packets A.center
        (enumerate A.labels l) i := by
  rw [A.grainPiece_enumerate, image_preimage_eq _ G.affine.surjective]

theorem grainPiece_outside (A : BlockAngularData D R G β τ)
    {j : Fin D.L} (hj : j ∉ R) (l : Fin A.labels.card) : A.grainPiece j l = ∅ := by
  simp [grainPiece, hj]

theorem grainPiece_measurable (A : BlockAngularData D R G β τ)
    (j : Fin D.L) (l : Fin A.labels.card) : MeasurableSet (A.grainPiece j l) := by
  unfold grainPiece
  split_ifs
  · exact (A.refinement.measurable_piece _ _).preimage
      G.affine.toContinuousAffineEquiv.continuous.measurable
  · exact MeasurableSet.empty

theorem grainPiece_subset (A : BlockAngularData D R G β τ)
    (j : Fin D.L) (l : Fin A.labels.card) : A.grainPiece j l ⊆ D.Hg j := by
  unfold grainPiece
  split_ifs with hj
  · intro q hq
    have hh := (A.refinement.1 (R.equivFin ⟨j, hj⟩)).2 hq.1
    have he : enumerate R (R.equivFin ⟨j, hj⟩) = j := by
      simp [WangZahlLot.Obl.wz_separated_cover_refinement.enumerate]
    change G.affine q ∈ G.affine '' D.Hg (enumerate R (R.equivFin ⟨j, hj⟩)) at hh
    rw [he] at hh
    exact (G.affine.injective.mem_set_image).mp hh
  · exact empty_subset _

theorem grainPiece_disjoint (A : BlockAngularData D R G β τ)
    (j : Fin D.L) (l l' : Fin A.labels.card) (hne : l ≠ l') :
    Disjoint (A.grainPiece j l) (A.grainPiece j l') := by
  unfold grainPiece
  split_ifs with hj
  · exact (A.refinement.piece_disjoint (R.equivFin ⟨j, hj⟩)
      ((enumerate_injective A.labels).ne hne)).preimage G.affine
  · simp

/-- The affine normalization changes all packet masses by the same
Jacobian, so returning to the original grains costs no mass. -/
theorem grainPiece_mass (A : BlockAngularData D R G β τ) (hδ : 0 < δ) :
    O (δ ^ τ) * ∑ j ∈ R, μ (D.Hg j) ≤ ∑ j, ∑ l, μ (A.grainPiece j l) := by
  classical
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hθ : 0 < A.scale := (by positivity : 0 < 2 * ρ).trans_le A.lower
  have ht (i : Fin R.card) : A.shade i ⊆ T (2 * ρ) (A.unitStart i) (unit (A.axis i)) :=
    (A.refinement.1 i).2.trans ((G.contained i).trans (A.unit_body_tube i))
  have hmass := A.refinement.piece_mass (x := A.unitStart) hθ A.lower A.unit_axis_norm ht
  change (∑ l ∈ A.labels, ∑ i, μ (packetPiece A.scale (fun i => unit (A.axis i))
    A.shade A.packets A.center l i)) = ∑ i, μ (A.shade i) at hmass
  let J := O (ρ / (64 * D.a * c ^ 2))
  have hJ0 : J ≠ 0 := by dsimp [J, O]; positivity
  have hJtop : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass' : J * (O (δ ^ τ) * ∑ j ∈ R, μ (D.Hg j)) ≤
      J * (∑ j, ∑ l, μ (A.grainPiece j l)) := by
    have hs : ∑ j, ∑ l, μ (A.grainPiece j l) =
        ∑ i : Fin R.card, ∑ l, μ (A.grainPiece (enumerate R i) l) := by
      rw [enumerate_sum R (fun j => ∑ l, μ (A.grainPiece j l))]
      symm
      apply Finset.sum_subset (Finset.subset_univ R)
      intro j _ hj
      simp [A.grainPiece_outside hj]
    have himage (i : Fin R.card) (l : Fin A.labels.card) :
        J * μ (A.grainPiece (enumerate R i) l) =
        μ (packetPiece A.scale (fun i => unit (A.axis i)) A.shade A.packets A.center
          (enumerate A.labels l) i) := by
      rw [A.grainPiece_enumerate]
      change O (ρ / (64 * D.a * c ^ 2)) * μ (G.affine ⁻¹' _) = _
      rw [← G.jacobian, image_preimage_eq _ G.affine.surjective]
    have htarget : J * (∑ j, ∑ l, μ (A.grainPiece j l)) = ∑ i, μ (A.shade i) := by
      rw [hs, Finset.mul_sum]
      simp_rw [Finset.mul_sum, himage]
      rw [Finset.sum_comm,
        enumerate_sum A.labels (fun l => ∑ i, μ (packetPiece A.scale
          (fun i => unit (A.axis i)) A.shade A.packets A.center l i)), hmass]
    have hsource : (∑ i, μ (D.normalizedShade R G.affine i)) =
        J * ∑ j ∈ R, μ (D.Hg j) := by
      simp only [ConcentratedGrainData.normalizedShade, G.jacobian]
      rw [← Finset.mul_sum, enumerate_sum R (fun j => μ (D.Hg j))]
    rw [htarget, mul_left_comm, ← hsource]
    exact A.mass
  have hh := mul_le_mul' (a := J⁻¹) le_rfl hmass'
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hJ0 hJtop, one_mul] using hh

/-- Each occupied pulled-back label contains whole old grains in one
flat prism in normalized coordinates. Its dimensions are uniform in the label. -/
theorem grainPiece_prism (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (hshort : G.short ≤ 1 / 8) (l : Fin A.labels.card)
    (hne : ∃ j, (A.grainPiece j l).Nonempty) :
    ∃ (z : V) (e : V ≃ₗᵢ[ℝ] V), ∀ j, (A.grainPiece j l).Nonempty →
      G.affine '' P D.a (ρ * c) c (D.z j) (D.e j) ⊆
        P (min (36 * G.short) (min (80 * A.scale) 4))
          (min (80 * A.scale) 4) 4 z e := by
  have hslab i : D.normalizedBody R G.affine i ⊆
      {q | |inner ℝ (boxAxis G.frame 0) q - inner ℝ (boxAxis G.frame 0) G.center| ≤
        G.short / 2} := by
    intro q hq
    have hh := (G.enclosure i hq).1
    change |G.frame (q - G.center) 0| ≤ _ at hh
    simpa only [mem_ofPred_eq, map_sub, PiLp.sub_apply, inner_boxAxis] using hh
  have hflat i : |inner ℝ (boxAxis G.frame 0) (unit (A.axis i))| ≤ 4 * G.short :=
    chord_unit_normal G.short_pos.le (A.lengths i).1
      (hslab i (A.endpoints i).1) (hslab i (A.endpoints i).2)
  have hoccupied {j : Fin D.L} (hj : (A.grainPiece j l).Nonempty) : j ∈ R := by
    by_contra hh
    rw [A.grainPiece_outside hh] at hj
    exact hj.ne_empty rfl
  have hne' : ∃ i, (packetPiece A.scale (fun i => unit (A.axis i))
      A.shade A.packets A.center (enumerate A.labels l) i).Nonempty := by
    obtain ⟨j, hj⟩ := hne
    obtain ⟨i, rfl⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective R
      (hoccupied hj)
    refine ⟨i, ?_⟩
    rw [← A.image_grainPiece i l]
    exact hj.image G.affine
  have hρ : 0 < ρ := (D.dimensions hδ).2.1
  obtain ⟨z, e, hbox⟩ := packet_piece_prism A.refinement G.short_pos.le hshort
    ((by positivity : 0 < 2 * ρ).trans_le A.lower) A.lower A.unit_axis_norm G.contained
    A.unit_body_tube G.unit_ball (boxAxis G.frame 0) (boxAxis_norm _ _) hslab hflat
    (enumerate A.labels l) hne'
  refine ⟨z, e, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective R
    (hoccupied hj)
  apply hbox i
  rw [← A.image_grainPiece i l]
  exact hj.image G.affine

end BlockAngularData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
