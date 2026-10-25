-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedEndpoint.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.EndpointPrisms
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedNarrow

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CappedEndpoint.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O I P T A bodyCount)
open WangZahlLot.Obl.wz_coarse_grains_assembly (rIdx rIdx_mem rIdx_injective)

/-- An upper point count normalized by the average incidence density. -/
def PrismData.HasCaps {n : ℕ} (D : PrismData n) (δ h ρ c : ℝ) : Prop :=
  ∃ m : Fin D.L → ℝ, (∀ j, 0 < m j) ∧
    (∀ j p, bodyCount (fun i => D.W i j) p ≤ m j) ∧
    ∀ j, O (δ ^ h * m j) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      ∑ i, volume (D.W i j)

/-- Whole-prism endpoint trimming preserves the normalized incidence caps. -/
theorem endpoint_clear_capped_prisms {ω ζ δ h h' ρ c R : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hR : 0 ≤ R)
    (hbudget : 4608 * (R + 2 * c + 6 * ρ) ≤ δ ^ (2 * h))
    (herr : O (δ ^ h') ≤ (1 / 2 : ENNReal) * O (δ ^ h))
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y 1) (hcap : D.HasCaps δ h ρ c) :
    ∃ D' : PrismData n, D'.a = D.a ∧ D'.Valid ω ζ δ h' ρ c x v Y 1 ∧
      D'.HasCaps δ h' ρ c ∧
      ∀ i j, (D'.W i j).Nonempty → ∀ p ∈ P D'.a (ρ * c) c (D'.z j) (D'.e j),
        R < dist p (x i) ∧ R < dist p (x i + v i) := by
  let J := Finset.univ.filter (fun j => D.Away ρ c R j)
  let f := rIdx J
  have hm := endpoint_prism_mass_retention D hδ hR hbudget hA H
  have hsum (i : Fin n) : ∑ j : Fin J.card, volume (D.W i (f j)) = ∑ j ∈ J, volume (D.W i j) := by
    calc
      _ = ∑ j : J, volume (D.W i j.val) := J.equivFin.symm.sum_comp _
      _ = _ := Finset.sum_coe_sort J (fun j => volume (D.W i j))
  have hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j)) := by
    simp_rw [hsum]
    exact (mul_le_mul' herr le_rfl).trans hm
  refine ⟨D.select D.s f id (D.γ ∘ f), rfl,
    valid_select_prisms D hδ hδ1 hhh H f (rIdx_injective J) hmass, ?_, ?_⟩
  · obtain ⟨m, hm, hcount, havg⟩ := hcap
    refine ⟨m ∘ f, fun j => hm (f j), fun j p => hcount (f j) p, ?_⟩
    intro j
    apply le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh)
        (hm (f j)).le)) le_rfl) (havg (f j))
  · intro i j hi p hp
    exact prism_endpoint_clearance D hδ (fun i => (hA.2.1 i).1) H hi
      (Finset.mem_filter.mp (rIdx_mem J j)).2 p hp

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
