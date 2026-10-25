import Submission.Obl.k4_scalar_candidate_original_return.Coverage.Family
import Submission.Obl.k4_scalar_candidate_original_return.Coverage.Pigeonhole

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return.PreparedData

open MeasureTheory Filter Set
open Submission.Lib.K4FinitePlankAtlases

noncomputable def familyCounts (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) : ℕ :=
  (a.greedy θ σ k ℓ i).length

noncomputable def familyPolys (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n)
    (j : Fin (a.familyCounts θ σ k ℓ i)) : Poly :=
  (a.greedy θ σ k ℓ i).get j

lemma family_piece_first (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (s : ℝ) (i : Fin (a.ls k ℓ).n)
    (j : Fin (a.familyCounts θ σ k ℓ i)) :
    (TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
      (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ×ˢ
      I (a.ls k ℓ).T ((a.ls k ℓ).time i)) =
    firstAssignment (fun j => a.candSet θ σ k ℓ i (a.familyPolys θ σ k ℓ i j)) j := by
  ext z
  simp only [TangentData.assignment, firstAssignment, candSet, tStart, tEnd,
    mem_prod, mem_inter_iff, mem_ofPred_eq]
  aesop

lemma family_piece_original (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (s : ℝ) (i : Fin (a.ls k ℓ).n)
    (j : Fin (a.familyCounts θ σ k ℓ i)) :
    (TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
      (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ×ˢ
      I (a.ls k ℓ).T ((a.ls k ℓ).time i)) =
    a.candSet θ σ k ℓ i ((a.greedy θ σ k ℓ i).get j) \
      ⋃ P ∈ (a.greedy θ σ k ℓ i).take j.val, a.candSet θ σ k ℓ i P := by
  rw [family_piece_first]
  exact firstAssignment_get _ _ j

lemma family_union (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (s : ℝ) (i : Fin (a.ls k ℓ).n) :
    (⋃ j : Fin (a.familyCounts θ σ k ℓ i),
      (TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
        (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ×ˢ
        I (a.ls k ℓ).T ((a.ls k ℓ).time i))) = a.cov θ σ k ℓ i := by
  calc
    _ = ⋃ j : Fin (a.familyCounts θ σ k ℓ i),
        firstAssignment (fun j => a.candSet θ σ k ℓ i (a.familyPolys θ σ k ℓ i j)) j := by
      congr 1
      funext j
      exact family_piece_first a θ σ k ℓ s i j
    _ = ⋃ j : Fin (a.familyCounts θ σ k ℓ i),
        a.candSet θ σ k ℓ i (a.familyPolys θ σ k ℓ i j) := iUnion_firstAssignment _
    _ = _ := by
      ext z
      constructor
      · intro hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        exact mem_iUnion₂.mpr ⟨_, List.get_mem _ _, hj⟩
      · intro hz
        obtain ⟨P, hP, hz⟩ := mem_iUnion₂.mp hz
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hP
        exact mem_iUnion.mpr ⟨j, by simpa only [familyPolys, hj] using hz⟩

lemma family_coverage (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (s : ℝ) (g : Fin (a.Wk k)) :
    {z : Inc | ∃ i j, (a.ls k ℓ).world i = g ∧
      z.1 ∈ TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
        (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ∧
      z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i)} = a.layerCoverage θ σ k ℓ g := by
  ext z
  constructor
  · rintro ⟨i, j, hi, hA, ht⟩
    have hz : z ∈ ⋃ j : Fin (a.familyCounts θ σ k ℓ i),
        (TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
          (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ×ˢ
          I (a.ls k ℓ).T ((a.ls k ℓ).time i)) := mem_iUnion.mpr ⟨j, hA, ht⟩
    rw [family_union] at hz
    exact mem_iUnion₂.mpr ⟨i, hi, hz⟩
  · intro hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
    rw [← family_union a θ σ k ℓ s i] at hz
    obtain ⟨j, hA, ht⟩ := mem_iUnion.mp hz
    exact ⟨i, j, hi, hA, ht⟩

variable {a : PreparedData} (ha : a.Valid)
include ha

lemma coverAt_of_layer (θ : ℝ) (hθ : 0 < θ) (σ : Scenario) (hc : 0 < σ.c₀)
    (R C : ℝ) (hR : (σ.R : ℝ) ≤ R) (k : ℕ) (ℓ : Fin (a.ct k))
    (s : ℝ) (hs0 : R⁻¹ ≤ s) (hs1 : s ≤ R)
    (hnear : |s - σ.s₀| ≤ θ * σ.c₀ / 4)
    (hhalf : |s - σ.s₀| ≤ σ.s₀ / 2) (hnode : a.nd k s = ℓ)
    (hmass : ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤ a.layerCoverageMass θ σ k ℓ) :
    a.tangentData.CoverAt R σ.s₀ σ.c₀ (θ * σ.c₀) C k := by
  have hN : 2 ≤ a.tangent k := ha.tangent_input.1 k
  have hN0 : 0 < a.tangent k := by linarith
  unfold TangentData.CoverAt
  refine ⟨s, hs0, hs1, hnear, hhalf, ?_⟩
  dsimp only [tangentData]
  rw [hnode]
  refine ⟨a.familyCounts θ σ k ℓ, a.familyPolys θ σ k ℓ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [familyCounts, mul_assoc] using greedy_length_le ha θ hθ σ hc k ℓ i
  · intro i j
    have hh := greedy_entry ha θ σ k ℓ i j
    refine ⟨hh.1.1, fun b => (hh.1.2 b).trans ?_⟩
    apply Real.rpow_le_rpow_of_exponent_le _ hR
    have hN := ha.tangent_input.1 k
    linarith
  · intro i j
    have hh := (greedy_entry ha θ σ k ℓ i j).2.2
    have hν := ((ha.exact k).2.1 (a.sm k)).2.2.2.1 ((a.ls k ℓ).world i)
    haveI := hν.1
    change _ ≤ a.ρ k ((a.ls k ℓ).world i)
      (TangentData.assignment (a.ls k ℓ) s (a.fitTol θ σ k)
        (a.familyCounts θ σ k ℓ) (a.familyPolys θ σ k ℓ) i j ×ˢ
        I (a.ls k ℓ).T ((a.ls k ℓ).time i))
    rw [family_piece_original]
    unfold thr at hh
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
    exact hh
  · unfold layerCoverageMass at hmass
    simp_rw [← family_coverage a θ σ k ℓ s] at hmass
    exact hmass

/-- Completed residual globalization, with the old centered priority regions unchanged. -/
theorem frequent_centered_cover (hSTI : STI) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ (R center c C : ℝ), 1 < R ∧ 0 < center ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ 1 ≤ C ∧
      ∃ᶠ k in atTop, a.tangentData.CoverAt R center c (θ * c) C k := by
  obtain ⟨σ, C, hs, hc, hC, hcov⟩ := frequent_positive_layer ha hSTI hθ hθ1
  let R : ℝ := 2 + (σ.R : ℝ) + 2 * σ.s₀ + 2 / σ.s₀ + σ.c₀ + σ.c₀⁻¹
  have hRn : 0 ≤ (σ.R : ℝ) := Nat.cast_nonneg _
  have hdiv : 0 < 2 / σ.s₀ := div_pos (by norm_num) hs
  have hinv : 0 < σ.c₀⁻¹ := inv_pos.mpr hc
  have hR1 : 1 < R := by dsimp [R]; linarith
  have hR0 : 0 < R := by linarith
  have hRcoef : (σ.R : ℝ) ≤ R := by dsimp [R]; linarith
  have hRc : σ.c₀ ≤ R := by dsimp [R]; linarith
  have hRcinv : R⁻¹ ≤ σ.c₀ := (inv_le_comm₀ hR0 hc).mpr (by dsimp [R]; linarith)
  have hRs : 2 * σ.s₀ ≤ R := by dsimp [R]; linarith
  have hRsinv : R⁻¹ ≤ σ.s₀ / 2 := by
    apply (inv_le_comm₀ hR0 (by positivity)).mpr
    have he : (σ.s₀ / 2)⁻¹ = 2 / σ.s₀ := by field_simp
    rw [he]
    dsimp [R]
    linarith
  refine ⟨R, σ.s₀, σ.c₀, C, hR1, hs, hRcinv, hRc, hC, ?_⟩
  exact hcov.mono fun k hk => by
    obtain ⟨ℓ, hℓ, hmass⟩ := hk
    obtain ⟨_, _, s, hnear, hhalf, hnode⟩ := hℓ
    have hlower := (abs_le.mp hhalf).1
    have hupper := (abs_le.mp hhalf).2
    exact coverAt_of_layer ha θ hθ σ hc R C hRcoef k ℓ s
      (hRsinv.trans (by linarith)) (by linarith) hnear hhalf hnode hmass

end Submission.Obl.k4_scalar_candidate_original_return.PreparedData
