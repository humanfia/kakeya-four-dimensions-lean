/- Adapted from this LOT tree o222, session x0774, commit 9dbb47a74d2ab640ef4d8807465d86d7e9066adc,
   Submission/Obl/k4_projected_parent_contact_reduction/StableBaseBudget.lean. -/
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

/-! Original parent mass and volume factors in the stable base-law recovery. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set

noncomputable section

/-- A partition discarded relative to the FULL parent law retains half of a
dense current row event. The current law is compared with the original law
before normalization. -/
theorem stable_partition_retains_parent {Ω ι : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (P G : Set Ω) (E : ι → Set Ω)
    (hG : G ⊆ P) {K m M η : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m) (hM : 0 < M)
    (hη : 0 ≤ η) (hmass : ENNReal.ofReal (m / M) ≤ ρ G)
    (hparent : μ P ≤ ENNReal.ofReal (K * m))
    (hloss : μ (P \ ⋃ i, E i) ≤ μ P * ENNReal.ofReal η)
    (hsmall : K * η ≤ 1 / (2 * M)) :
    ENNReal.ofReal (m / (2 * M)) ≤ ρ (G ∩ ⋃ i, E i) := by
  have hcover : ρ G ≤ ρ (G ∩ ⋃ i, E i) + μ (P \ ⋃ i, E i) := by
    calc
      _ ≤ ρ ((G ∩ ⋃ i, E i) ∪ (P \ ⋃ i, E i)) := by
        apply measure_mono
        intro z hz
        by_cases he : z ∈ ⋃ i, E i
        · exact Or.inl ⟨hz, he⟩
        · exact Or.inr ⟨hG hz, he⟩
      _ ≤ ρ (G ∩ ⋃ i, E i) + ρ (P \ ⋃ i, E i) := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl (hρ _)
  have hdeleted : μ (P \ ⋃ i, E i) ≤ ENNReal.ofReal ((m / M) / 2) := by
    calc
      _ ≤ μ P * ENNReal.ofReal η := hloss
      _ ≤ ENNReal.ofReal (K * m) * ENNReal.ofReal η := mul_le_mul' hparent le_rfl
      _ = ENNReal.ofReal ((K * m) * η) := (ENNReal.ofReal_mul (mul_nonneg hK hm)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h := mul_le_mul_of_nonneg_left hsmall hm
        calc
          (K * m) * η = m * (K * η) := by ring
          _ ≤ m * (1 / (2 * M)) := h
          _ = (m / M) / 2 := by ring
  have h := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (ρ G) (ρ (G ∩ ⋃ i, E i)) (μ (P \ ⋃ i, E i)) (m / M)
    (by positivity) hmass hcover hdeleted
  simpa only [div_div, mul_comm M (2 : ℝ)] using h

/-- The native factor `a^d` in the recovered cap cancels the ORIGINAL full
parent prior. The row chart contributes its exact `|λ| q³g` inverse Jacobian. -/
theorem row_base_budget_cancel {a d q g prior K T lam : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hg : 0 < g) (hK : 0 < K) (hT : 0 ≤ T)
    (hprior : a ^ d * q ^ 2 * g / K ≤ prior) :
    27 * T * (K * a ^ d) * (|lam| * q ^ 3 * g) / (q * prior) ≤
      27 * T * K ^ 2 * |lam| := by
  have hap : 0 < a ^ d := Real.rpow_pos_of_pos ha _
  have hpriorp : 0 < prior := lt_of_lt_of_le (by positivity) hprior
  have hmass : a ^ d * q ^ 2 * g ≤ prior * K := (div_le_iff₀ hK).mp hprior
  have hratio : a ^ d * q ^ 3 * g / (q * prior) ≤ K := by
    apply (div_le_iff₀ (mul_pos hq hpriorp)).mpr
    calc
      a ^ d * q ^ 3 * g = (a ^ d * q ^ 2 * g) * q := by ring
      _ ≤ (prior * K) * q := mul_le_mul_of_nonneg_right hmass hq.le
      _ = K * (q * prior) := by ring
  calc
    _ = (27 * T * K * |lam|) * (a ^ d * q ^ 3 * g / (q * prior)) := by ring
    _ ≤ (27 * T * K * |lam|) * K :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
