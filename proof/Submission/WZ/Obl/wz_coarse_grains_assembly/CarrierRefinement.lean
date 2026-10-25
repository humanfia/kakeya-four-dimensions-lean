-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.CarrierRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.CarrierNet
import Submission.WZ.Obl.wz_coarse_grains_assembly.ColorRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory Metric

/-- A fixed loss suffices to put the retained tubes in one half-radius
carrier, while keeping a fixed fraction of multiplicity at every retained
point. The constant is uniform in the fine radius and the family size. -/
theorem exists_uniform_carrier_refinement :
    ∃ K : ℕ, 0 < K ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ I) →
      (∀ i, MeasurableSet (Y i)) →
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (y w : V),
        ‖w‖ = 1 ∧
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
        (∀ i ∈ S, T δ (x i) (v i) ⊆ T (1 / 2) y w) ∧
        (∑ i, μ (Y i)) ≤ (K : ENNReal) ^ 2 * ∑ i ∈ S, μ (Z i) ∧
        ∀ p, (∃ i ∈ S, p ∈ Z i) →
          q n {i | p ∈ Y i} ≤ K * q n {i | i ∈ S ∧ p ∈ Z i} := by
  classical
  obtain ⟨K, hK, y, w, hw, hcover⟩ := exists_finite_half_carriers
  refine ⟨K, hK, ?_⟩
  intro δ hδ hδ1 n x v Y hT hY
  have hx (i : Fin n) : ‖x i‖ ≤ 1 := by
    apply le_of_lt
    apply mem_ball_zero_iff.mp
    exact (hT i).2 (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
  choose color hcolor using fun i => hcover δ hδ1 (x i) (v i) (hx i) (hT i).1
  obtain ⟨a, Z, hZ, hmass, hfrac⟩ := color_refinement hK color Y hY
  let S : Finset (Fin n) := Finset.univ.filter (fun i => color i = a)
  have hS (i : Fin n) : i ∈ S ↔ color i = a := by simp [S]
  have hempty (i : Fin n) (hi : i ∉ S) : Z i = ∅ :=
    (hZ i).2.2 (fun hc => hi ((hS i).mpr hc))
  have hsum : (∑ i ∈ S, μ (Z i)) = ∑ i, μ (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    rw [hempty i hi]
    exact measure_empty
  refine ⟨S, Z, y a, w a, hw a, ?_, ?_, ?_, ?_⟩
  · exact fun i => ⟨(hZ i).1, (hZ i).2.1, hempty i⟩
  · intro i hi
    simpa only [(hS i).mp hi] using hcolor i
  · rwa [hsum]
  · intro p hp
    have he : {i | i ∈ S ∧ p ∈ Z i} = {i | p ∈ Z i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · exact And.right
      · intro hi
        refine ⟨?_, hi⟩
        by_contra hn
        rw [hempty i hn] at hi
        exact hi
    rw [he]
    obtain ⟨i, _, hi⟩ := hp
    exact hfrac p ⟨i, hi⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
