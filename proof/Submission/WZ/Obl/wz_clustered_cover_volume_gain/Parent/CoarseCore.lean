-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiberCore
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PacketSupport

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- A packet estimate for dense cores controls the original global fine level.
Only an upper bound inside each packet is needed. -/
theorem global_level_bound_of_packet_estimate {n N L : ℕ} {δ b H r M B Cc : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hM : 0 ≤ M) (hB : 0 < B)
    (S : Finset (Fin n)) (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hsupport : ∀ i, (Y i).Nonempty → i ∈ S ∧ f i ∈ U)
    (hpos : 0 < ∑ i, volume (Y i))
    (hdense : ENNReal.ofReal (δ ^ r * n * δ ^ 2) ≤ ∑ i, volume (Y i))
    (hsmall : 4 * δ ^ (H - r) ≤ 1)
    (hlower : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal M ≤ multiplicity Y p)
    (hupper : ∀ p, multiplicity Y p ≤ ENNReal.ofReal (2 * M))
    (hpacket : ∀ p j, fiberMultiplicity (g ∘ f) Y j p ≤ ENNReal.ofReal B)
    (hcoarse : ∀ W : Fin n → Set Space, (∀ i, W i ⊆ Y i) →
      (∃ j, (packetShading b S W f U g j).Nonempty) →
      (∀ k ∈ U, (∃ i ∈ S, f i = k ∧ (W i).Nonempty) →
        ENNReal.ofReal (δ ^ H * (S.filter fun i => f i = k).card * δ ^ 2) ≤
          ∑ i ∈ S with f i = k, volume (W i)) →
      (∀ p ∈ ⋃ j, packetUnion S W f U g j,
        ENNReal.ofReal ((M / 4) / B) ≤ multiplicity (packetUnion S W f U g) p) →
      (M / 4) / B ≤ Cc) :
    ∀ p, multiplicity Y p ≤ ENNReal.ofReal (8 * B * Cc) := by
  have hoff (i) (hi : i ∉ S) : Y i = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    exact fun hne => hi (hsupport i hne).1
  obtain ⟨W, hW, hmass, hWdens, hWlevel⟩ :=
    dense_fiber_core hδ hM S f U Y hY hfin hoff hdense hsmall hlower
  have hWsub (i) : W i ⊆ Y i := (hW i).2
  have hWsupport (i) (hi : (W i).Nonempty) : i ∈ S ∧ f i ∈ U :=
    hsupport i (hi.mono (hWsub i))
  have hWpos : 0 < ∑ i, volume (W i) := by
    refine lt_of_lt_of_le ?_ hmass
    exact ENNReal.mul_pos (by norm_num) hpos.ne'
  have hoccupied := occupied_packet_of_positive_mass hb S W f U g hWsupport hWpos
  have hWpacket (p) (j) : fiberMultiplicity (g ∘ f) W j p ≤ ENNReal.ofReal B :=
    (fiberMultiplicity_mono (g ∘ f) hWsub j p).trans (hpacket p j)
  have hlevel := packet_lower_of_fine_level (g ∘ f) W (packetUnion S W f U g)
    (packetUnion_cover S W f U g hWsupport)
    (packetUnion_union S W f U g hWsupport).subset hB hWlevel hWpacket
  have hnum := hcoarse W hWsub hoccupied hWdens hlevel
  have hMbound : 2 * M ≤ 8 * B * Cc := by
    have hh := (div_le_iff₀ hB).mp hnum
    nlinarith
  intro p
  exact (hupper p).trans (ENNReal.ofReal_le_ofReal hMbound)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
