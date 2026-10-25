-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoarseShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ShadingExpansion
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismCarrier
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.AssignedCover
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoverWeights

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

/-- The coarse shading attached to one assigned box. -/
def packetShading {n N L : ℕ} (b : ℝ) (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L) (j : Fin L) : Set Space :=
  thickening b (⋃ i ∈ S.filter (fun i => f i ∈ U ∧ g (f i) = j), Z i)

theorem packetShading_measurable {n N L : ℕ} (b : ℝ) (S : Finset (Fin n))
    (Z : Fin n → Set Space) (f : Fin n → Fin N) (U : Finset (Fin N))
    (g : Fin N → Fin L) (j : Fin L) : MeasurableSet (packetShading b S Z f U g j) :=
  isOpen_thickening.measurableSet

namespace Interfaces

/-- Complete selected fine fibers give a dense shading in each enlarged factoring carrier. -/
theorem factored_coarse_shading {δ η h ρ K m a b H : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g)
    (hdense : ∀ k ∈ U,
      o (δ ^ H * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
        ∑ i ∈ S with f i = k, μ (Z i)) :
    ∀ j : Fin L,
      MeasurableSet (packetShading b S Z f U g j) ∧
      packetShading b S Z f U g j ⊆
        Carrier 8 (3 * b) (z j - (1 / 2 : ℝ) • (e j).symm (EuclideanSpace.single 2 1))
          ((e j).symm (EuclideanSpace.single 2 1)) ∧
      o (δ ^ H * b ^ 2) ≤ μ (packetShading b S Z f U g j) := by
  classical
  intro j
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  let wj : V := (e j).symm (EuclideanSpace.single 2 1)
  have hew : e j wj = EuclideanSpace.single 2 1 := (e j).apply_symm_apply _
  have hbox : P a b 8 (z j) (e j) ⊆ Carrier 8 (2 * b) (z j - (1 / 2 : ℝ) • wj) wj :=
    box_subset_carrier hcover.ordered hb (by norm_num) (z j) (e j) hew
  have hsub : (⋃ i ∈ S.filter (fun i => f i ∈ U ∧ g (f i) = j), Z i) ⊆
      P a b 8 (z j) (e j) := by
    intro p hp
    rcases mem_iUnion.mp hp with ⟨i, hp⟩
    rcases mem_iUnion.mp hp with ⟨hi, hp⟩
    obtain ⟨hiS, hiU, hij⟩ := Finset.mem_filter.mp hi
    have hc := hcover.covers (f i) hiU
    rw [hij] at hc
    change p ∈ Factor.box a b 8 (z j) (e j)
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using
      hc (hC.2.2.2.1 i hiS ((hA.2.1 i).2.2.2 ((hC.1 i).2.1 hp)))
  have hcarrier : packetShading b S Z f U g j ⊆
      Carrier 8 (3 * b) (z j - (1 / 2 : ℝ) • wj) wj := by
    refine (thickening_subset_of_subset b (hsub.trans hbox)).trans ?_
    simpa only [Carrier, Tube, show b + 2 * b = 3 * b by ring] using
      thickening_thickening_subset b (2 * b)
        (segment ℝ (z j - (1 / 2 : ℝ) • wj + ((1 - 8) / 2) • wj)
          (z j - (1 / 2 : ℝ) • wj + ((1 - 8) / 2) • wj + (8 : ℝ) • wj))
  have hpacket : (U.filter fun k => g k = j).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hr := hcover.rich j
    rw [hz, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero] at hr
    have hp : 0 < m * (a * b * (2 * 4)) := by
      exact mul_pos hcover.coefficient_pos (by positivity)
    linarith
  obtain ⟨k, hk⟩ := hpacket
  obtain ⟨hkU, hkj⟩ := Finset.mem_filter.mp hk
  obtain ⟨i, hiS, hfi⟩ := c_fibers_nonempty hδ hA hC k
  have hF : (S.filter fun i => f i = k).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hiS, hfi⟩⟩
  have hd : ENNReal.ofReal (δ ^ H * (S.filter fun i => f i = k).card * δ ^ 2) ≤
      ∑ i ∈ S with f i = k, volume (Z i) := by
    simpa only [o, μ, q, ← Finset.coe_filter, Set.ncard_coe_finset] using hdense k hkU
  have hd' := thickening_family_shading_dense (S.filter fun i => f i = k) hF hδ
    (hδρ.trans (hcover.width.trans hcover.ordered)) (Real.rpow_nonneg hδ.le H)
    (fun i hi => (hA.2.1 i).1)
    (fun i hi => (hC.1 i).2.1.trans (hA.2.1 i).2.2.2) hd
  refine ⟨packetShading_measurable _ _ _ _ _ _ _, hcarrier, hd'.trans (measure_mono ?_)⟩
  apply thickening_subset_of_subset
  intro p hp
  rcases mem_iUnion.mp hp with ⟨i, hp⟩
  rcases mem_iUnion.mp hp with ⟨hi, hp⟩
  obtain ⟨hiS, hfi⟩ := Finset.mem_filter.mp hi
  apply mem_iUnion.mpr ⟨i, ?_⟩
  exact mem_iUnion.mpr ⟨Finset.mem_filter.mpr
    ⟨hiS, by simpa only [hfi] using hkU, by simpa only [hfi] using hkj⟩, hp⟩

end Interfaces

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
