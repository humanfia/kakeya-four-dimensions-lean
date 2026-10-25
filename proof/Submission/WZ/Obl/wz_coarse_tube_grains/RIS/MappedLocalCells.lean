-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.MappedLocalCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalCells

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open wz_extremal_lipschitz_grains
open scoped Classical

/-- Bounded-cell localization after a homeomorphism, keeping all partition
pieces and their crossing counts in the original space. -/
theorem mapped_bounded_partition_localization (F : Space ≃ₜ Space)
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) {G : ℕ}
    (E : Fin G → Set Space) (c : Fin G → Space)
    (hE : ∀ j, MeasurableSet (E j))
    (hbound : ∀ j, E j ⊆ F ⁻¹' closedBall (F (c j)) R)
    (hdisj : Pairwise fun j k => Disjoint (E j) (E k)) :
    ∃ (N : ℕ) (D : Fin N → Set Space) (q : Fin N → Space) (parent : Fin N → Fin G),
      (∀ i, MeasurableSet (D i) ∧ D i ⊆ E (parent i) ∧ D i ⊆ F ⁻¹' ball (F (q i)) r) ∧
      (Pairwise fun i k => Disjoint (D i) (D k)) ∧
      (⋃ i, D i) = ⋃ j, E j ∧
      (N : ℝ) ≤ G * (12 * R / r) ^ 3 ∧
      ∀ W : Set Space,
        ({i | (W ∩ D i).Nonempty}.ncard : ℝ) ≤
          (12 * R / r) ^ 3 * ({j | (W ∩ E j).Nonempty}.ncard : ℝ) := by
  have hdisj' : Pairwise fun j k => Disjoint (F '' E j) (F '' E k) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    rintro p ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    exact Set.disjoint_left.mp (hdisj hjk) ha (F.injective he ▸ hb)
  obtain ⟨N, D', q', parent, hD, hDdisj, hunion, hN, hcount⟩ :=
    bounded_partition_localization hr hrR (fun j => F '' E j) (fun j => F (c j))
      (fun j => F.measurableEmbedding.measurableSet_image.mpr (hE j))
      (fun j p hp => by obtain ⟨z, hz, rfl⟩ := hp; exact hbound j hz) hdisj'
  let D := fun i => F ⁻¹' D' i
  let q := fun i => F.symm (q' i)
  have himage (i : Fin N) : F '' D i = D' i := image_preimage_eq _ F.surjective
  have hne (A B : Set Space) : (F '' A ∩ F '' B).Nonempty ↔ (A ∩ B).Nonempty := by
    rw [← image_inter F.injective]
    exact image_nonempty
  refine ⟨N, D, q, parent, ?_, ?_, ?_, hN, ?_⟩
  · intro i
    refine ⟨(hD i).1.preimage F.continuous.measurable, ?_, ?_⟩
    · intro p hp
      obtain ⟨z, hz, he⟩ := (hD i).2.1 hp
      exact F.injective he ▸ hz
    · intro p hp
      have hh := (hD i).2.2 hp
      simpa only [q, F.apply_symm_apply, Set.mem_preimage] using hh
  · intro i k hik
    exact (hDdisj hik).preimage F
  · have hh := congrArg (fun A : Set Space => F ⁻¹' A) hunion
    simpa only [preimage_iUnion, preimage_image_eq _ F.injective] using hh
  · intro W
    have hh := hcount (F '' W)
    simp_rw [← himage, hne] at hh
    exact hh

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
