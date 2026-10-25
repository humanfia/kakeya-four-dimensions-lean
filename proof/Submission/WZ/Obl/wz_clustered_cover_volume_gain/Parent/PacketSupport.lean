-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.PacketSupport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RefinedCoarseMultiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- Supported fine shadings lie in their assigned packet unions. -/
theorem packetUnion_cover {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L)
    (hsupport : ∀ i, (Z i).Nonempty → i ∈ S ∧ f i ∈ U) (i : Fin n) :
    Z i ⊆ packetUnion S Z f U g (g (f i)) := by
  intro p hp
  obtain ⟨hiS, hiU⟩ := hsupport i ⟨p, hp⟩
  exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hiU, rfl⟩, hp⟩

theorem packetUnion_union {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L)
    (hsupport : ∀ i, (Z i).Nonempty → i ∈ S ∧ f i ∈ U) :
    (⋃ j, packetUnion S Z f U g j) = ⋃ i, Z i := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨j, hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨i, _, hp⟩ := Set.mem_iUnion₂.mp hp
    exact Set.mem_iUnion.mpr ⟨i, hp⟩
  · apply Set.iUnion_subset
    intro i
    exact (packetUnion_cover S Z f U g hsupport i).trans (Set.subset_iUnion _ _)

theorem occupied_packet_of_positive_mass {n N L : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin n)) (Z : Fin n → Set Space) (f : Fin n → Fin N)
    (U : Finset (Fin N)) (g : Fin N → Fin L)
    (hsupport : ∀ i, (Z i).Nonempty → i ∈ S ∧ f i ∈ U)
    (hmass : 0 < ∑ i, volume (Z i)) :
    ∃ j, (packetShading b S Z f U g j).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hmass
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
  refine ⟨g (f i), p, mem_thickening_iff.mpr ?_⟩
  exact ⟨p, packetUnion_cover S Z f U g hsupport i hp, by simpa using hb⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
