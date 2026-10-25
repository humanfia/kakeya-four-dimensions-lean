-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismCores.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedCores
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Interfaces

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

private noncomputable def diagonalCoordinates (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) :
    Space ≃L[ℝ] Space :=
  ({ toFun := fun p => WithLp.toLp 2 (fun i => p i / s i)
     invFun := fun p => WithLp.toLp 2 (fun i => p i * s i)
     left_inv := by intro p; ext i; exact div_mul_cancel₀ (p i) (hs i)
     right_inv := by intro p; ext i; exact mul_div_cancel_right₀ (p i) (hs i)
     map_add' := by intro p q; ext i; exact add_div _ _ _
     map_smul' := by intro r p; ext i; change (r * p i) / s i = r * (p i / s i); ring } :
    Space ≃ₗ[ℝ] Space).toContinuousLinearEquiv

/-- Separated prisms can capture a constant fraction of any bounded measurable
set in their central eighths. The constant is independent of all three side
lengths and the frame, and the measure can count total shading mass. -/
theorem exists_disjoint_prism_cores :
    ∃ D : ℕ, 0 < D ∧ ∀ (a b c : ℝ), 0 < a → 0 < b → 0 < c →
      ∀ (e : Space ≃ₗᵢ[ℝ] Space) (μ : Measure Space) {E : Set Space},
      MeasurableSet E → TotallyBounded E →
      ∃ F : Finset Space, (↑F : Set Space) ⊆ E ∧
        (↑F : Set Space).PairwiseDisjoint (fun z => Interfaces.P a b c z e) ∧
        μ E ≤ (D : ENNReal) *
          μ (E ∩ ⋃ z ∈ F, Interfaces.P (a / 8) (b / 8) (c / 8) z e) := by
  classical
  obtain ⟨D, hD, hselect⟩ := exists_separated_small_cores
  refine ⟨D, hD, ?_⟩
  intro a b c ha hb hc e μ E hEm hEt
  let s : Fin 3 → ℝ := ![a, b, c]
  have hs : ∀ i, 0 < s i := by intro i; fin_cases i <;> assumption
  let A : Space ≃L[ℝ] Space := e.toContinuousLinearEquiv.trans
    (diagonalCoordinates s (fun i => (hs i).ne'))
  have hbox (p z : Space) (hp : p ∈ Interfaces.P a b c z e) :
      dist (A p) (A z) ≤ 1 := by
    rw [dist_eq_norm, ← map_sub]
    have hp' (i : Fin 3) : |e (p - z) i| ≤ s i / 2 := by
      fin_cases i
      · exact hp.1
      · exact hp.2.1
      · exact hp.2.2
    have hcoord (i : Fin 3) : |A (p - z) i| ≤ 1 / 2 := by
      change |e (p - z) i / s i| ≤ 1 / 2
      rw [abs_div, abs_of_pos (hs i)]
      apply (div_le_iff₀ (hs i)).mpr
      linarith [hp' i]
    have hsq := EuclideanSpace.real_norm_sq_eq (A (p - z))
    rw [Fin.sum_univ_three] at hsq
    have h0 := sq_le_sq₀ (abs_nonneg (A (p - z) 0)) (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mpr (hcoord 0)
    have h1 := sq_le_sq₀ (abs_nonneg (A (p - z) 1)) (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mpr (hcoord 1)
    have h2 := sq_le_sq₀ (abs_nonneg (A (p - z) 2)) (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mpr (hcoord 2)
    simp only [sq_abs] at h0 h1 h2
    nlinarith [norm_nonneg (A (p - z))]
  have hcore (p z : Space) (hp : dist (A p) (A z) ≤ 1 / 32) :
      p ∈ Interfaces.P (a / 8) (b / 8) (c / 8) z e := by
    rw [dist_eq_norm, ← map_sub] at hp
    have hcoord (i : Fin 3) : |e (p - z) i| ≤ s i / 32 := by
      have hnorm : |A (p - z) i| ≤ ‖A (p - z)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A (p - z)) i
      have hh : |A (p - z) i| ≤ 1 / 32 := hnorm.trans hp
      change |e (p - z) i / s i| ≤ 1 / 32 at hh
      rw [abs_div, abs_of_pos (hs i)] at hh
      have h := (div_le_iff₀ (hs i)).mp hh
      linarith
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    change |e (p - z) 0| ≤ a / 8 / 2 ∧ |e (p - z) 1| ≤ b / 8 / 2 ∧
      |e (p - z) 2| ≤ c / 8 / 2
    change |e (p - z) 0| ≤ a / 32 at h0
    change |e (p - z) 1| ≤ b / 32 at h1
    change |e (p - z) 2| ≤ c / 32 at h2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hAE : MeasurableSet (A '' E) :=
    A.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hEm
  obtain ⟨G, hGE, hGsep, hmass⟩ := hselect (Measure.map A μ) hAE
    (hEt.image A.toContinuousLinearMap.uniformContinuous)
  let F : Finset Space := G.image A.symm
  have hFE : (↑F : Set Space) ⊆ E := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨p', hpE, rfl⟩ := hGE hq
    simpa only [A.symm_apply_apply] using hpE
  have hFdisj : (↑F : Set Space).PairwiseDisjoint (fun z => Interfaces.P a b c z e) := by
    intro p hp q hq hpq
    obtain ⟨p', hpG, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hqG, rfl⟩ := Finset.mem_image.mp hq
    have hdist := hGsep p' hpG q' hqG (fun h => hpq (congrArg A.symm h))
    apply Set.disjoint_left.mpr
    intro z hzp hzq
    have hzp' := hbox z (A.symm p') hzp
    have hzq' := hbox z (A.symm q') hzq
    simp only [A.apply_symm_apply] at hzp' hzq'
    have hh := dist_triangle p' (A z) q'
    rw [dist_comm p' (A z)] at hh
    linarith
  have hm : MeasurableSet (A '' E ∩ ⋃ p ∈ G, closedBall p (1 / 32)) :=
    hAE.inter (G.measurableSet_biUnion fun _ _ => measurableSet_closedBall)
  rw [Measure.map_apply A.continuous.measurable hAE,
    Measure.map_apply A.continuous.measurable hm,
    Set.preimage_inter, Set.preimage_image_eq _ A.injective] at hmass
  refine ⟨F, hFE, hFdisj, hmass.trans ?_⟩
  apply mul_le_mul_right
  apply measure_mono
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp hp.2
  refine ⟨hp.1, mem_iUnion₂.mpr ⟨A.symm q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩⟩
  apply hcore
  simpa only [A.apply_symm_apply, mem_closedBall, dist_comm] using hpq

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
