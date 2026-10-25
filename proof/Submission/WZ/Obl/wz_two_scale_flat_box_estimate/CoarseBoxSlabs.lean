-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.CoarseBoxSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.CoarseBoxGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseSlabs

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodySlabCount)

/-- The global fine slab estimate passes to contracted boxes using assigned
incidences, even when the intermediate tubes leave the unit ball. -/
lemma coarse_box_slabs {δ l F D : ℝ} (hl : 0 ≤ l) (hF : 0 < F) (hD : 0 ≤ D)
    {n q : ℕ} (x v : Fin n → Space) (U : Fin q → Set Space) (R : Fin n → Fin q → Prop)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hslab : SlabCount δ l n x v)
    (hlower : ∀ j, F ≤ (Set.ncard {i | R i j} : ℝ))
    (hupper : ∀ i, (Set.ncard {j | R i j} : ℝ) ≤ 1)
    (hsize : (n : ℝ) ≤ D * q * F)
    (hcontain : ∀ i j, R i j → boxContraction '' Tube δ (x i) (v i) ⊆ U j) :
    BodySlabCount U (512 * D * l) := by
  intro u s r hu hr
  let V := ball (0 : Space) 1 ∩ {p | |inner ℝ u p - 64 * s| ≤ 64 * r}
  let P := fun i => Tube δ (x i) (v i) ⊆ V
  let S := fun j => U j ⊆ {p | |inner ℝ u p - s| ≤ r}
  have himp : ∀ i j, S j → R i j → P i := by
    intro i j hj hij p hp
    refine ⟨hball i hp, ?_⟩
    have hh := hj (hcontain i j hij ⟨p, hp, rfl⟩)
    have he := (WangZahlLot.Obl.wz_nonflat_factored_improvement.smul_mem_slab_iff
      (by norm_num : (0 : ℝ) < 1 / 64) u p s r).mp hh
    change |inner ℝ u p - 64 * s| ≤ 64 * r
    convert he using 1 <;> ring
  have hcount := WangZahlLot.Obl.wz_nonflat_factored_improvement.bounded_incidence_count
    R P S (by norm_num : (0 : ℝ) ≤ 1) (fun j _ => hlower j) hupper himp
  have hraw : (Set.ncard {i | P i} : ℝ) ≤ 512 * l * n * r := by
    have hh := (hslab u (64 * s) (64 * r) hu (by positivity)).trans
      (mul_le_mul' le_rfl (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu
        (64 * s) (64 * r) (by positivity)))
    rw [← ENNReal.ofReal_mul (by positivity)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    change (Set.ncard {i | P i} : ℝ) ≤ _ at hh'
    nlinarith only [hh']
  apply ENNReal.ofReal_le_ofReal
  change (Set.ncard {j | S j} : ℝ) ≤ (512 * D * l) * (q : ℝ) * r
  apply (mul_le_mul_iff_left₀ hF).mp
  have hh := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 512 * l * r)
  nlinarith only [hcount, hraw, hh]

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
