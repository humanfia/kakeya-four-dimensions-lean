-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.DensitySplit.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, DensitySplit.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O I P ballDensity
  ballDensity_measurable ballDensity_mass half_mass_after_loss)

/-- Split fine incidences by the density of the original union in a ball.
Both alternatives retain half of the original prism incidence mass. -/
theorem prism_incidence_density_split {ω ζ δ h ρ c R lam : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hR : 0 < R) (hY : ∀ i, MeasurableSet (Y i)) (hYI : ∀ i, Y i ⊆ I)
    (H : D.Valid ω ζ δ h ρ c x v Y 1) :
    (∃ Z : Fin n → Set V, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤ ∑ i, volume (Z i) ∧
      ∀ i p, p ∈ Z i → O (lam * R ^ 3) ≤ volume ((⋃ i, Y i) ∩ ball p R)) ∨
    ∃ B : Set V, MeasurableSet B ∧ B ⊆ ⋃ i, Y i ∧
      (∀ p ∈ B, volume ((⋃ i, Y i) ∩ ball p R) ≤ O (lam * R ^ 3)) ∧
      (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤
        ∑ i, ∑ j, volume (D.W i j ∩ B) := by
  classical
  let U := ⋃ i, Y i
  let F := {p | p ∈ U ∧ lam ≤ ballDensity U R p}
  let B := U \ F
  let Z := fun i => (⋃ j, D.W i j) ∩ F
  have hUm : MeasurableSet U := MeasurableSet.iUnion hY
  have hFm : MeasurableSet F := hUm.inter
    (measurableSet_le measurable_const (ballDensity_measurable hUm R))
  have hBm : MeasurableSet B := hUm.diff hFm
  have hW := H.2.2.2.2.1
  have hZm (i : Fin n) : MeasurableSet (Z i) :=
    (MeasurableSet.iUnion fun j => (hW i j).1).inter hFm
  have hZY (i : Fin n) : Z i ⊆ Y i := inter_subset_left.trans
    (iUnion_subset fun j => (hW i j).2.1.trans inter_subset_left)
  have hWU (i : Fin n) (j : Fin D.L) : D.W i j ⊆ U :=
    (hW i j).2.1.trans (inter_subset_left.trans (subset_iUnion Y i))
  have htotalfin : (∑ i, ∑ j, volume (D.W i j)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hW i j).2.1.trans (inter_subset_left.trans (hYI i))))
  by_cases hlarge : (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤
      ∑ i, volume (Z i)
  · refine Or.inl ⟨Z, fun i => ⟨hZm i, hZY i⟩, hlarge, ?_⟩
    intro i p hp
    rw [← ballDensity_mass U p hR]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hp.2.2 (by positivity))
  · refine Or.inr ⟨B, hBm, sdiff_subset, ?_, ?_⟩
    · intro p hp
      have hh : ballDensity U R p ≤ lam := le_of_lt (lt_of_not_ge fun hh => hp.2 ⟨hp.1, hh⟩)
      rw [← ballDensity_mass U p hR]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hh (by positivity))
    · apply half_mass_after_loss htotalfin ?_ (le_of_lt (lt_of_not_ge hlarge))
      have heq (i : Fin n) : volume (Z i) = ∑ j, volume (D.W i j ∩ F) := by
        rw [show Z i = ⋃ j, D.W i j ∩ F by exact iUnion_inter _ _]
        simpa only [tsum_fintype] using measure_iUnion (μ := volume) (fun j j' hne =>
          ((hW i j).2.2 j' hne).mono inter_subset_left inter_subset_left)
          (fun j => (hW i j).1.inter hFm)
      simp_rw [heq]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      have hsub : D.W i j ⊆ (D.W i j ∩ B) ∪ (D.W i j ∩ F) := by
        intro p hp
        by_cases hpF : p ∈ F
        · exact Or.inr ⟨hp, hpF⟩
        · exact Or.inl ⟨hp, hWU i j hp, hpF⟩
      exact (measure_mono hsub).trans (measure_union_le _ _)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
