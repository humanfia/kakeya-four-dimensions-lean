import Submission.Obl.k4_scalar_candidate_original_return.Core.Globalize

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return.PreparedData

open MeasureTheory Filter Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def layerCoverage (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) (g : Fin (a.Wk k)) : Set Inc :=
  ⋃ (i : Fin (a.ls k ℓ).n) (_ : (a.ls k ℓ).world i = g), a.cov θ σ k ℓ i

noncomputable def layerCoverageMass (a : PreparedData) (θ : ℝ) (σ : Scenario)
    (k : ℕ) (ℓ : Fin (a.ct k)) : ENNReal :=
  ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g (a.layerCoverage θ σ k ℓ g)

noncomputable def activeLayer (a : PreparedData) (θ : ℝ) (n k : ℕ)
    (ℓ : Fin (a.ct k)) : Prop :=
  0 < (menu n).s₀ ∧ 0 < (menu n).c₀ ∧ ℓ ∈ a.layersOf θ (menu n) k

noncomputable def activeLayerSet (a : PreparedData) (θ : ℝ) (n k : ℕ)
    (ℓ : Fin (a.ct k)) (g : Fin (a.Wk k)) : Set Inc := by
  classical
  exact if a.activeLayer θ n k ℓ then a.layerCoverage θ (menu n) k ℓ g else ∅

lemma covJ_eq_layers (a : PreparedData) (θ : ℝ) (J k : ℕ) (g : Fin (a.Wk k)) :
    a.CovJ θ J k g = ⋃ n : Fin J, ⋃ ℓ, a.activeLayerSet θ n.val k ℓ g := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hs, hc, ℓ, hℓ, hz⟩ :
        ∃ n, n < J ∧ 0 < (menu n).s₀ ∧ 0 < (menu n).c₀ ∧
          ∃ ℓ ∈ a.layersOf θ (menu n) k, z ∈ a.layerCoverage θ (menu n) k ℓ g := by
      simpa only [CovJ, Cov, layerCoverage, mem_iUnion, exists_prop] using hz
    refine mem_iUnion.mpr ⟨⟨n, hn⟩, mem_iUnion.mpr ⟨ℓ, ?_⟩⟩
    simpa only [activeLayerSet, if_pos (show a.activeLayer θ n k ℓ from ⟨hs, hc, hℓ⟩)] using hz
  · intro hz
    obtain ⟨n, ℓ, hz⟩ := mem_iUnion.mp hz |>.imp (fun _ h => mem_iUnion.mp h)
    have hpos : a.activeLayer θ n.val k ℓ := by
      by_contra hn
      simpa only [activeLayerSet, if_neg hn, mem_empty_iff_false] using hz
    have hz' : z ∈ a.layerCoverage θ (menu n.val) k ℓ g := by
      simpa only [activeLayerSet, if_pos hpos] using hz
    have hx : ∃ n, n < J ∧ 0 < (menu n).s₀ ∧ 0 < (menu n).c₀ ∧
        ∃ ℓ ∈ a.layersOf θ (menu n) k, z ∈ a.layerCoverage θ (menu n) k ℓ g :=
      ⟨n.val, n.isLt, hpos.1, hpos.2.1, ℓ, hpos.2.2, hz'⟩
    simpa only [CovJ, Cov, layerCoverage, mem_iUnion, exists_prop] using hx

lemma covMass_le_layer_sum (a : PreparedData) (θ : ℝ) (J k : ℕ) :
    a.covMass θ J k ≤ ∑ n : Fin J, ∑ ℓ : Fin (a.ct k),
      if a.activeLayer θ n.val k ℓ then a.layerCoverageMass θ (menu n.val) k ℓ else 0 := by
  classical
  have hμ (g : Fin (a.Wk k)) : a.ρ k g (a.CovJ θ J k g) ≤
      ∑ n : Fin J, ∑ ℓ : Fin (a.ct k), a.ρ k g (a.activeLayerSet θ n.val k ℓ g) := by
    rw [covJ_eq_layers]
    exact (measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun n _ => measure_iUnion_fintype_le _ _)
  unfold covMass
  calc
    _ ≤ ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
        ∑ n : Fin J, ∑ ℓ : Fin (a.ct k), a.ρ k g (a.activeLayerSet θ n.val k ℓ g) :=
      Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hμ g)
    _ = ∑ n : Fin J, ∑ ℓ : Fin (a.ct k),
        ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
          a.ρ k g (a.activeLayerSet θ n.val k ℓ g) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      ext n
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro ℓ _
      by_cases h : a.activeLayer θ n.val k ℓ
      · simp only [activeLayerSet, if_pos h, layerCoverageMass]
      · simp only [activeLayerSet, if_neg h, measure_empty, mul_zero, Finset.sum_const_zero]

variable {a : PreparedData} (ha : a.Valid)
include ha

lemma exists_large_layer (θ : ℝ) (J k : ℕ)
    (hm : ENNReal.ofReal ((4 * a.H k)⁻¹) < a.covMass θ J k) :
    ∃ n : Fin J, ∃ ℓ : Fin (a.ct k), a.activeLayer θ n.val k ℓ ∧
      ENNReal.ofReal ((4 * ((J : ℝ) + 1) * a.H k ^ 2)⁻¹) <
        a.layerCoverageMass θ (menu n.val) k ℓ := by
  classical
  by_contra h
  push Not at h
  have hsum := covMass_le_layer_sum a θ J k
  have hsum' : a.covMass θ J k ≤
      ∑ _n : Fin J, ∑ _ℓ : Fin (a.ct k),
        ENNReal.ofReal ((4 * ((J : ℝ) + 1) * a.H k ^ 2)⁻¹) := by
    apply hsum.trans
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro ℓ _
    split
    · exact h n ℓ ‹_›
    · exact bot_le
  have hH : 2 ≤ a.H k := (ha.bounds k).2.2.1
  have hct : (a.ct k : ℝ) ≤ a.H k := (ha.bounds k).2.2.2.2.2.2.2.2.2.1
  have hnum : (J : ℝ) * (a.ct k : ℝ) /
      (4 * ((J : ℝ) + 1) * a.H k ^ 2) ≤ (4 * a.H k)⁻¹ := by
    have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hct hJ
    have hmul' := mul_le_mul_of_nonneg_right hmul (show 0 ≤ a.H k by linarith)
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hbound : (∑ _n : Fin J, ∑ _ℓ : Fin (a.ct k),
      ENNReal.ofReal ((4 * ((J : ℝ) + 1) * a.H k ^ 2)⁻¹)) ≤
      ENNReal.ofReal ((4 * a.H k)⁻¹) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast J, ← ENNReal.ofReal_natCast (a.ct k),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg (a.ct k)),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg J)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [div_eq_mul_inv, mul_assoc] using hnum
  exact (not_lt_of_ge (hsum'.trans hbound)) hm

lemma frequent_positive_layer (hSTI : STI) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ (σ : Scenario) (C : ℝ), 0 < σ.s₀ ∧ 0 < σ.c₀ ∧ 1 ≤ C ∧
      ∃ᶠ k in atTop, ∃ ℓ : Fin (a.ct k), ℓ ∈ a.layersOf θ σ k ∧
        ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤ a.layerCoverageMass θ σ k ℓ := by
  obtain ⟨J, hJ⟩ := exists_covering_menu ha hSTI hθ hθ1
  have hh : ∃ᶠ k in atTop, ∃ n : Fin J, ∃ ℓ : Fin (a.ct k),
      a.activeLayer θ n.val k ℓ ∧
      ENNReal.ofReal ((4 * ((J : ℝ) + 1) * a.H k ^ 2)⁻¹) <
        a.layerCoverageMass θ (menu n.val) k ℓ := hJ.mono fun k hk => exists_large_layer ha θ J k hk
  obtain ⟨n, hn⟩ := frequently_exists.mp hh
  obtain ⟨k, ℓ, hpos, hmass⟩ := hn.exists
  refine ⟨menu n.val, 4 * ((J : ℝ) + 1), hpos.1, hpos.2.1, ?_, ?_⟩
  · have : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
    linarith
  · exact hn.mono fun k hk => by
      obtain ⟨ℓ, hpos, hmass⟩ := hk
      exact ⟨ℓ, hpos.2.2, hmass.le⟩

end Submission.Obl.k4_scalar_candidate_original_return.PreparedData
