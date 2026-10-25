/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeTimeLists.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarSupport
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

/-- The actual finite native blocks meeting one scalar time cell form a list
of at most nine blocks, including all closed interval endpoints. -/
theorem exists_native_contact_time_blocks (T : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσq : σ ≤ ((2 : ℝ) ^ T)⁻¹) (τ : ℝ) :
    ∃ J : Finset (Fin (2 ^ T)), (J.card : ℝ) ≤ 9 ∧
      ∀ (j : Fin (2 ^ T)) (t : ℝ), |t - τ| ≤ σ → t ∈ I T j → j ∈ J := by
  classical
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  obtain ⟨J, hJ, hcover⟩ := exists_contact_time_blocks hq hσ hσq τ
  let J' := Finset.univ.filter fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ) ∈ J
  have hinj : Function.Injective (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.natCast_inj.mp hij)
  refine ⟨J', ?_, ?_⟩
  · have hsub : J'.image (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ)) ⊆ J := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hj).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc
    exact (by exact_mod_cast hc : (J'.card : ℝ) ≤ J.card).trans hJ
  · intro j t ht hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hcover ((j : ℕ) : ℤ) t ht ?_ ?_⟩
    · simpa only [I, mem_Icc, div_eq_mul_inv, Int.cast_natCast] using hj.1
    · simpa only [I, mem_Icc, div_eq_mul_inv, Int.cast_natCast] using hj.2

/-- Aggregate native lists over the two time-block coordinates. This costs at
most eighty-one, independently of the total numbers of original blocks. -/
theorem card_list_of_contact_time_blocks {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T₀ T : ℕ)
    (parentBlock : ι → Fin (2 ^ T₀)) (childBlock : ι → Fin (2 ^ T))
    {σ τ L : ℝ} (hσ : 0 ≤ σ)
    (hσ₀ : σ ≤ ((2 : ℝ) ^ T₀)⁻¹) (hσ₁ : σ ≤ ((2 : ℝ) ^ T)⁻¹)
    (hL : 0 ≤ L)
    (hcontact : ∀ i ∈ S, ∃ t : ℝ,
      |t - τ| ≤ σ ∧ t ∈ I T₀ (parentBlock i) ∧ t ∈ I T (childBlock i))
    (hcount : ∀ j₀ j,
      ((S.filter fun i => parentBlock i = j₀ ∧ childBlock i = j).card : ℝ) ≤ L) :
    (S.card : ℝ) ≤ 81 * L := by
  classical
  obtain ⟨J₀, hJ₀, hmem₀⟩ := exists_native_contact_time_blocks T₀ hσ hσ₀ τ
  obtain ⟨J, hJ, hmem⟩ := exists_native_contact_time_blocks T hσ hσ₁ τ
  let F := fun z : Fin (2 ^ T₀) × Fin (2 ^ T) =>
    S.filter fun i => parentBlock i = z.1 ∧ childBlock i = z.2
  have hsub : S ⊆ (J₀ ×ˢ J).biUnion F := by
    intro i hi
    obtain ⟨t, ht, ht₀, ht₁⟩ := hcontact i hi
    exact Finset.mem_biUnion.mpr ⟨(parentBlock i, childBlock i),
      Finset.mem_product.mpr ⟨hmem₀ _ t ht ht₀, hmem _ t ht ht₁⟩,
      Finset.mem_filter.mpr ⟨hi, rfl, rfl⟩⟩
  calc
    _ ≤ (((J₀ ×ˢ J).biUnion F).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ z ∈ J₀ ×ˢ J, ((F z).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ J₀ ×ˢ J, L := by
      exact Finset.sum_le_sum fun z _ => hcount z.1 z.2
    _ = (J₀.card : ℝ) * (J.card : ℝ) * L := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
    _ ≤ 81 * L := by
      have hh : (J₀.card : ℝ) * (J.card : ℝ) ≤ 81 :=
        (mul_le_mul hJ₀ hJ (Nat.cast_nonneg _) (by norm_num)).trans_eq (by norm_num)
      exact mul_le_mul_of_nonneg_right hh hL

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
