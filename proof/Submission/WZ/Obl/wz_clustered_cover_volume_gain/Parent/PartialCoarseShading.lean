-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.PartialCoarseShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseShading
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseCounts

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

/-- Fiber density is only needed for occupied fibers to make each occupied
packet neighborhood dense. Empty packets require no density hypothesis. -/
theorem packetShading_dense_of_occupied_fibers {δ b ℓ : ℝ} {n N L : ℕ}
    (S : Finset (Fin n)) (x v : Fin n → Space) (Z : Fin n → Set Space)
    (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L)
    (hδ : 0 < δ) (hδb : δ ≤ b) (hℓ : 0 ≤ ℓ)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hZ : ∀ i ∈ S, Z i ⊆ Tube δ (x i) (v i))
    (hdense : ∀ k ∈ U, (∃ i ∈ S, f i = k ∧ (Z i).Nonempty) →
      ENNReal.ofReal (ℓ * (S.filter fun i => f i = k).card * δ ^ 2) ≤
        ∑ i ∈ S with f i = k, volume (Z i)) :
    ∀ j, (packetShading b S Z f U g j).Nonempty →
      ENNReal.ofReal (ℓ * b ^ 2) ≤ volume (packetShading b S Z f U g j) := by
  classical
  intro j hj
  obtain ⟨q, hq⟩ := hj
  obtain ⟨p, hp, _⟩ := mem_thickening_iff.mp hq
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨hiS, hiU, hij⟩ := Finset.mem_filter.mp hi
  have hF : (S.filter fun i' => f i' = f i).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hiS, rfl⟩⟩
  have hd := thickening_family_shading_dense (S.filter fun i' => f i' = f i) hF hδ hδb hℓ
    (fun i' hi' => hv i' (Finset.mem_filter.mp hi').1)
    (fun i' hi' => hZ i' (Finset.mem_filter.mp hi').1)
    (hdense (f i) hiU ⟨i, hiS, rfl, p, hpi⟩)
  refine hd.trans (measure_mono (thickening_subset_of_subset b ?_))
  intro p hp
  obtain ⟨i', hi', hp⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨hiS', hfi⟩ := Finset.mem_filter.mp hi'
  exact Set.mem_iUnion₂.mpr ⟨i', Finset.mem_filter.mpr
    ⟨hiS', hfi ▸ hiU, hfi ▸ hij⟩, hp⟩

namespace Interfaces

/-- Any subshading of the covered fine family remains in the factoring carrier. -/
theorem factored_packetShading_subset {δ η h ρ K m a b : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z Z' : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g)
    (hsub : ∀ i, Z' i ⊆ Z i) (j : Fin L) :
    packetShading b S Z' f U g j ⊆ factoringCarrier b (z j) (e j) := by
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  let wj : V := (e j).symm (EuclideanSpace.single 2 1)
  have hew : e j wj = EuclideanSpace.single 2 1 := (e j).apply_symm_apply _
  have hbox : P a b 8 (z j) (e j) ⊆ Carrier 8 (2 * b) (z j - (1 / 2 : ℝ) • wj) wj :=
    box_subset_carrier hcover.ordered hb (by norm_num) (z j) (e j) hew
  have hpack : (⋃ i ∈ S.filter (fun i => f i ∈ U ∧ g (f i) = j), Z' i) ⊆
      P a b 8 (z j) (e j) := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨hiS, hiU, hij⟩ := Finset.mem_filter.mp hi
    have hc := hcover.covers (f i) hiU
    rw [hij] at hc
    change p ∈ Factor.box a b 8 (z j) (e j)
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using
      hc (hC.2.2.2.1 i hiS ((hA.2.1 i).2.2.2 ((hC.1 i).2.1 (hsub i hp))))
  refine (thickening_subset_of_subset b (hpack.trans hbox)).trans ?_
  simpa only [factoringCarrier, wj, Carrier, Tube, show b + 2 * b = 3 * b by ring] using
    thickening_thickening_subset b (2 * b)
      (segment ℝ (z j - (1 / 2 : ℝ) • wj + ((1 - 8) / 2) • wj)
        (z j - (1 / 2 : ℝ) • wj + ((1 - 8) / 2) • wj + (8 : ℝ) • wj))

end Interfaces

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
