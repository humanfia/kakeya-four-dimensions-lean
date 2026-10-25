-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.NeighborhoodMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LocalMultiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

/-- A common neighborhood preserves a uniform lower multiplicity bound. -/
theorem thickening_multiplicity_lower {N : ℕ} {Y : Fin N → Set Space}
    {M : ENNReal} (hM : ∀ p ∈ ⋃ j, Y j, M ≤ multiplicity Y p) (r : ℝ) :
    ∀ q ∈ ⋃ j, thickening r (Y j), M ≤ multiplicity (fun j => thickening r (Y j)) q := by
  classical
  intro q hq
  obtain ⟨j, hq⟩ := mem_iUnion.mp hq
  obtain ⟨p, hp, hqp⟩ := mem_thickening_iff.mp hq
  refine (hM p (mem_iUnion.mpr ⟨j, hp⟩)).trans ?_
  apply Finset.sum_le_sum
  intro k _
  by_cases hpk : p ∈ Y k
  · have hqk : q ∈ thickening r (Y k) := mem_thickening_iff.mpr ⟨p, hpk, hqp⟩
    simp only [Set.indicator_of_mem hpk, Set.indicator_of_mem hqk, le_refl]
  · simp only [Set.indicator_of_notMem hpk]
    exact bot_le

/-- Cutting all shadings by the same multiplicity level keeps its lower bound. -/
theorem multiplicity_lower_on_common_cut {N : ℕ} (Y : Fin N → Set Space) (G : Set Space)
    {M : ENNReal} (hG : ∀ p ∈ G, M ≤ multiplicity Y p) :
    ∀ p ∈ ⋃ j, Y j ∩ G, M ≤ multiplicity (fun j => Y j ∩ G) p := by
  classical
  intro p hp
  obtain ⟨j, hpj⟩ := mem_iUnion.mp hp
  have hmult : multiplicity (fun j => Y j ∩ G) p = multiplicity Y p := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : p ∈ Y k <;> simp [Set.indicator, hk, hpj.2]
  rw [hmult]
  exact hG p hpj.2

theorem factoringCarrier_volume_upper {b : ℝ} (hb : 0 < b) (hb3 : b ≤ 1 / 3)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    volume (factoringCarrier b z e) ≤ ENNReal.ofReal (360 * b ^ 2) := by
  have hsub := carrier_subset_box (by norm_num : (0 : ℝ) ≤ 8) z e
    (e.apply_symm_apply (EuclideanSpace.single 2 (1 : ℝ))) (ρ := 3 * b)
  calc
    _ ≤ volume (Factor.box (2 * (3 * b)) (2 * (3 * b)) (8 + 2 * (3 * b)) z e) := measure_mono hsub
    _ = ENNReal.ofReal ((2 * (3 * b)) * (2 * (3 * b)) * (8 + 2 * (3 * b))) :=
      Factor.box_volume (by positivity) (by positivity) (by positivity) _ _
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hb3 (sq_nonneg b)
      nlinarith

/-- A coarse volume estimate bounds a uniform multiplicity level on the original
packet unions, because the same lower level persists throughout their neighborhoods. -/
theorem coarse_multiplicity_bound_of_union_lower {b c M : ℝ} (hb : 0 < b)
    (hb3 : b ≤ 1 / 3) (hc : 0 < c) (hM : 0 ≤ M) {N : ℕ} (hN : 0 < N)
    (Q : Fin N → Set Space) (z : Fin N → Space) (e : Fin N → Space ≃ₗᵢ[ℝ] Space)
    (hsub : ∀ j, thickening b (Q j) ⊆ factoringCarrier b (z j) (e j))
    (hmult : ∀ p ∈ ⋃ j, Q j, ENNReal.ofReal M ≤ multiplicity Q p)
    (hvol : ENNReal.ofReal (c * (N * b ^ 2)) ≤ volume (⋃ j, thickening b (Q j))) :
    M ≤ 360 / c := by
  have hmass : (∑ j, volume (thickening b (Q j))) ≤ ENNReal.ofReal (360 * (N * b ^ 2)) := by
    calc
      _ ≤ ∑ _j : Fin N, ENNReal.ofReal (360 * b ^ 2) := Finset.sum_le_sum fun j _ =>
        (measure_mono (hsub j)).trans (factoringCarrier_volume_upper hb hb3 (z j) (e j))
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hh : ENNReal.ofReal (M * (c * (N * b ^ 2))) ≤ ENNReal.ofReal (360 * (N * b ^ 2)) := by
    rw [ENNReal.ofReal_mul hM]
    exact (mul_le_mul_right hvol _).trans
      ((multiplicity_mul_volume_le_mass (fun j => isOpen_thickening.measurableSet)
        (thickening_multiplicity_lower hmult b)).trans hmass)
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hNb : 0 < (N : ℝ) * b ^ 2 := by positivity
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hNb).mp
  simpa only [mul_assoc] using hr

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
