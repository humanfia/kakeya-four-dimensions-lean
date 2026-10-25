-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeDomainLists.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Mathlib

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

noncomputable section

theorem finiteMenuUnion_card {ι γ : Type*} [DecidableEq γ]
    (S : Finset ι) (lists : ι → Finset γ) {A B : ℝ}
    (hS : (S.card : ℝ) ≤ A) (hB : 0 ≤ B)
    (hcount : ∀ i ∈ S, ((lists i).card : ℝ) ≤ B) :
    ((S.biUnion lists).card : ℝ) ≤ A * B := by
  classical
  have hcard : (S.biUnion lists).card ≤ ∑ i ∈ S, (lists i).card := Finset.card_biUnion_le
  calc
    _ ≤ ∑ i ∈ S, ((lists i).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum hcount
    _ = (S.card : ℝ) * B := by simp
    _ ≤ A * B := mul_le_mul_of_nonneg_right hS hB

def domainListUnion {ι κ γ : Type*} [Fintype ι]
    (decode : ι → κ) (S : Finset κ) (lists : ι → Finset γ) : Finset γ := by
  classical
  exact (Finset.univ.filter fun i => decode i ∈ S).biUnion lists

theorem domainListUnion_card {ι κ γ : Type*} [Fintype ι]
    (decode : ι → κ) (hinj : Function.Injective decode)
    (S : Finset κ) (lists : ι → Finset γ) {A B : ℝ}
    (hS : (S.card : ℝ) ≤ A) (hB : 0 ≤ B)
    (hcount : ∀ i, ((lists i).card : ℝ) ≤ B) :
    ((domainListUnion decode S lists).card : ℝ) ≤ A * B := by
  classical
  let R := Finset.univ.filter fun i => decode i ∈ S
  have hsub : R.image decode ⊆ S := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  have hR : R.card ≤ S.card := by
    rw [← Finset.card_image_of_injective R hinj]
    exact Finset.card_le_card hsub
  have hcard : (domainListUnion decode S lists).card ≤ ∑ i ∈ R, (lists i).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ ∑ i ∈ R, ((lists i).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _i ∈ R, B := Finset.sum_le_sum fun i _ => hcount i
    _ = (R.card : ℝ) * B := by simp
    _ ≤ A * B := mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hR).trans hS) hB

theorem mem_domainListUnion {ι κ γ : Type*} [Fintype ι]
    (decode : ι → κ) (S : Finset κ) (lists : ι → Finset γ)
    {i : ι} (hi : decode i ∈ S) {j : γ} (hj : j ∈ lists i) :
    j ∈ domainListUnion decode S lists := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hj⟩

end
end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
