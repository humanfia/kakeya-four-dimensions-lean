-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedCores.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ParameterPacking
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.WeightedSelection

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Any bounded measurable set has a fixed-fraction refinement in small cores
whose centres are far apart. The measure is arbitrary, so it can be the sum of
shading measures. An anisotropic coordinate change then gives separated prism
cores without a loss depending on their aspect ratio. -/
theorem exists_separated_small_cores :
    ∃ D : ℕ, 0 < D ∧ ∀ (μ : Measure Space) {E : Set Space},
      MeasurableSet E → TotallyBounded E →
      ∃ F : Finset Space, (↑F : Set Space) ⊆ E ∧
        (∀ p ∈ F, ∀ q ∈ F, p ≠ q → 2 < dist p q) ∧
        μ E ≤ (D : ENNReal) * μ (E ∩ ⋃ p ∈ F, closedBall p (1 / 32)) := by
  classical
  obtain ⟨M, hM⟩ := separated_family_card_bound
    (isCompact_closedBall (0 : Space) 2).totallyBounded (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨max 1 M, by omega, ?_⟩
  intro μ E hEm hEt
  obtain ⟨C, hCE, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      hEt (by norm_num : (0 : ℝ) < 1 / 32)
  let R : C → C → Prop := fun p q => dist (p : Space) q ≤ 2
  have hdegree (p : C) : (Finset.univ.filter (R p)).card ≤ max 1 M := by
    let G := Finset.univ.filter (R p)
    let f : Fin G.card → Space := fun j => ((G.equivFin.symm j).val : Space) - p
    have hinj : Function.Injective (fun j : Fin G.card => ((G.equivFin.symm j).val : Space)) :=
      Subtype.val_injective.comp (Subtype.val_injective.comp G.equivFin.symm.injective)
    have hc (j : Fin G.card) : f j ∈ closedBall (0 : Space) 2 := by
      have hj := (Finset.mem_filter.mp (G.equivFin.symm j).property).2
      change dist (p : Space) ((G.equivFin.symm j).val : Space) ≤ 2 at hj
      simpa only [f, mem_closedBall, dist_zero_left, ← dist_eq_norm, dist_comm] using hj
    have hs (i j : Fin G.card) (hij : i ≠ j) : 1 / 32 ≤ dist (f i) (f j) := by
      have he := hsep ((G.equivFin.symm i).val : Space) (G.equivFin.symm i).val.property
        ((G.equivFin.symm j).val : Space) (G.equivFin.symm j).val.property
        (fun h => hij (hinj h))
      simpa only [f, dist_sub_right] using he.le
    exact (hM f hc hs).trans (le_max_right _ _)
  let w : C → ENNReal := fun p => μ (E ∩ closedBall p (1 / 32))
  obtain ⟨S, -, hSsep, hmass⟩ := weighted_separated_subfamily R
    (fun p => by dsimp [R]; simp) (fun h => by simpa only [R, dist_comm] using h)
    (max 1 M) hdegree w Finset.univ
  let F : Finset Space := S.image (fun p : C => (p : Space))
  have hFsep : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → 2 < dist p q := by
    intro p hp q hq hpq
    obtain ⟨p', hpS, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hqS, rfl⟩ := Finset.mem_image.mp hq
    exact lt_of_not_ge (hSsep p' hpS q' hqS (fun h => hpq (congrArg Subtype.val h)))
  have hdisj : (S : Set C).PairwiseDisjoint (fun p => E ∩ closedBall (p : Space) (1 / 32)) := by
    intro p hp q hq hpq
    apply Disjoint.mono inter_subset_right inter_subset_right
    apply closedBall_disjoint_closedBall
    have hdist : 2 < dist (p : Space) q := lt_of_not_ge (hSsep p hp q hq hpq)
    linarith
  have hsum : (∑ p ∈ S, w p) = μ (E ∩ ⋃ p ∈ F, closedBall p (1 / 32)) := by
    rw [← measure_biUnion_finset hdisj (fun p _ => hEm.inter measurableSet_closedBall)]
    congr 1
    ext p
    simp only [F, Finset.mem_image, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨q, hq, hpE, hpq⟩
      exact ⟨hpE, q, ⟨q, hq, rfl⟩, hpq⟩
    · rintro ⟨hpE, q, ⟨q', hq', rfl⟩, hpq⟩
      exact ⟨q', hq', hpE, hpq⟩
  have hstart : μ E ≤ ∑ p : C, w p := by
    have hsub : E ⊆ ⋃ p : C, E ∩ closedBall (p : Space) (1 / 32) := by
      intro p hp
      obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hcover hp)
      exact mem_iUnion.mpr ⟨⟨q, hq⟩, hp, hpq⟩
    exact (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
  refine ⟨F, ?_, hFsep, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hCE q.property
  · exact (hstart.trans hmass).trans_eq (by rw [hsum])

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
