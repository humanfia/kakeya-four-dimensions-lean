-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PacketClusters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketLabels
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LongGeometry

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain.Parent (Carrier)
open scoped Classical

/-- The packet labels form a finite carrier family, with exact mass,
bounded duplication for each fine tube and the packet overlap bound. -/
theorem PacketRefinement.finite_clusters {n : ℕ} {β δ θ : ℝ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hθ : 0 < θ) (hδθ : δ ≤ θ) (hv : ∀ i, ‖v i‖ = 1)
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    (hball : ∀ i, Z i ⊆ Metric.ball (0 : Space) 1) :
    ∃ y w : {ℓ // ℓ ∈ packetLabelUniverse θ x v} → Space,
      (∀ ℓ, ‖w ℓ‖ = 1) ∧
      (∀ ℓ i, (packetPiece θ v Z P a ℓ.val i).Nonempty →
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Carrier 6 (8 * θ) (y ℓ) (w ℓ)) ∧
      (∀ p, ({ℓ : {ℓ // ℓ ∈ packetLabelUniverse θ x v} |
        ∃ i, p ∈ packetPiece θ v Z P a ℓ.val i}.ncard : ℝ) ≤ 2 * θ ^ (-β)) ∧
      (∀ i, ({ℓ : {ℓ // ℓ ∈ packetLabelUniverse θ x v} |
        (packetPiece θ v Z P a ℓ.val i).Nonempty}.ncard : ℝ) ≤ (2 * 6 ^ 3 * 22 ^ 3 : ℝ)) ∧
      (∑ ℓ : {ℓ // ℓ ∈ packetLabelUniverse θ x v}, ∑ i,
        volume (packetPiece θ v Z P a ℓ.val i)) = ∑ i, volume (Z i) := by
  classical
  let Λ := packetLabelUniverse θ x v
  have hcar (ℓ : {ℓ // ℓ ∈ Λ}) : ∃ y w : Space, ‖w‖ = 1 ∧
      ∀ i, (packetPiece θ v Z P a ℓ.val i).Nonempty →
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Carrier 6 (8 * θ) y w := by
    by_cases hne : ∃ i, (packetPiece θ v Z P a ℓ.val i).Nonempty
    · obtain ⟨z, w, hw, hsub⟩ := h.piece_carrier hθ hδθ hv hZT hball ℓ.val hne
      refine ⟨z + (5 / 2 : ℝ) • w, w, hw, ?_⟩
      intro i hi
      have he : z + (5 / 2 : ℝ) • w + ((1 - (6 : ℝ)) / 2) • w = z := by module
      change Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.thickening (8 * θ) (segment ℝ
          (z + (5 / 2 : ℝ) • w + ((1 - (6 : ℝ)) / 2) • w)
          (z + (5 / 2 : ℝ) • w + ((1 - (6 : ℝ)) / 2) • w + (6 : ℝ) • w))
      rw [he]
      exact hsub i hi
    · refine ⟨0, EuclideanSpace.single 0 (1 : ℝ), by simp, ?_⟩
      intro i hi
      exact (hne ⟨i, hi⟩).elim
  choose y w hw hcar using hcar
  refine ⟨y, w, hw, hcar, ?_, ?_, ?_⟩
  · intro p
    have hfin : {ℓ : PacketLabel | ∃ i, p ∈ packetPiece θ v Z P a ℓ i}.Finite := by
      apply Λ.finite_toSet.subset
      rintro ℓ ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h.piece_label hθ hδθ hv hZT hi⟩
    have hinj := Set.ncard_le_ncard_of_injOn (fun ℓ : {ℓ // ℓ ∈ Λ} => ℓ.val)
      (s := {ℓ : {ℓ // ℓ ∈ Λ} | ∃ i, p ∈ packetPiece θ v Z P a ℓ.val i})
      (t := {ℓ : PacketLabel | ∃ i, p ∈ packetPiece θ v Z P a ℓ i})
      (fun _ hh => hh) Subtype.val_injective.injOn hfin
    exact (Nat.cast_le.mpr (hinj.trans (h.piece_label_count p))).trans (h.card_bound hθ p)
  · intro i
    have hinj := Set.ncard_le_ncard_of_injOn (fun ℓ : {ℓ // ℓ ∈ Λ} => ℓ.val)
      (s := {ℓ : {ℓ // ℓ ∈ Λ} | (packetPiece θ v Z P a ℓ.val i).Nonempty})
      (t := (wz_balanced_cluster_cover.labelBox θ 2 (x i) (v i) : Set PacketLabel))
      (by rintro ℓ ⟨p, hp⟩; exact h.piece_label hθ hδθ hv hZT hp)
      Subtype.val_injective.injOn (Finset.finite_toSet _)
    have hb := wz_balanced_cluster_cover.card_labelBox_le hθ (by norm_num : (0 : ℝ) ≤ 2) (x i) (v i)
    rw [Set.ncard_coe_finset] at hinj
    exact (Nat.cast_le.mpr hinj).trans (by norm_num at hb ⊢; exact hb)
  · calc
      _ = ∑ ℓ ∈ Λ, ∑ i, volume (packetPiece θ v Z P a ℓ i) :=
        Finset.sum_coe_sort Λ (fun ℓ => ∑ i, volume (packetPiece θ v Z P a ℓ i))
      _ = _ := h.piece_mass hθ hδθ hv hZT

end WangZahlLot.Obl.wz_broad_grains_initialization
