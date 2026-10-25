/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/FractionCleanup.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 072b775c1cfdd16b3b0fc7205a3bd163553f049d,
Submission/Obl/k4_scalar_mesh_projection/FractionCleanup.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching

/-- There are only boundedly many intercept choices at an original state.
Removing low fractional choices therefore loses a controlled amount of
the original reference mass, independent of the number of states. -/
theorem select_state_groups_with_fraction_floor {Q I : Type*} [DecidableEq I]
    (F : Finset Q) (G : Q → Finset I) (w : Q → ℝ) (m : Q → I → ℝ)
    (δ L : ℝ) (hδ : 0 ≤ δ) (hw : ∀ q ∈ F, 0 ≤ w q)
    (hcount : ∀ q ∈ F, ((G q).card : ℝ) ≤ L) :
    ∃ H : Q → Finset I,
      (∀ q, H q ⊆ G q) ∧ (∀ q, ∀ i ∈ H q, δ * w q ≤ m q i) ∧
      (∑ q ∈ F, ∑ i ∈ G q \ H q, m q i) ≤ δ * L * (∑ q ∈ F, w q) := by
  classical
  let H : Q → Finset I := fun q => (G q).filter fun i => δ * w q ≤ m q i
  have hsub (q : Q) : H q ⊆ G q := Finset.filter_subset _ _
  have hfloor (q : Q) (i : I) (hi : i ∈ H q) : δ * w q ≤ m q i :=
    (Finset.mem_filter.mp hi).2
  have hrow (q : Q) (hq : q ∈ F) :
      (∑ i ∈ G q \ H q, m q i) ≤ δ * w q * L := by
    have hlight (i : I) (hi : i ∈ G q \ H q) : m q i ≤ δ * w q := by
      apply le_of_lt
      apply lt_of_not_ge
      intro h
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, h⟩)
    have hcard0 : ((G q \ H q).card : ℝ) ≤ ((G q).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : G q \ H q ⊆ G q))
    calc
      _ ≤ ∑ _i ∈ G q \ H q, δ * w q := Finset.sum_le_sum hlight
      _ = δ * w q * ((G q \ H q).card : ℝ) := by simp [mul_comm]
      _ ≤ δ * w q * L :=
        mul_le_mul_of_nonneg_left (hcard0.trans (hcount q hq)) (mul_nonneg hδ (hw q hq))
  refine ⟨H, hsub, hfloor, ?_⟩
  calc
    _ ≤ ∑ q ∈ F, δ * w q * L := Finset.sum_le_sum hrow
    _ = δ * L * (∑ q ∈ F, w q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- States or groups with excessive relative loss are charged to the
actual removed mass. The retained pieces have their explicit old floor. -/
theorem select_pieces_with_small_fractional_loss {I : Type*} [DecidableEq I]
    (F : Finset I) (a b : I → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hba : ∀ i ∈ F, b i ≤ a i) :
    ∃ H : Finset I, H ⊆ F ∧ (∀ i ∈ H, (1 - θ) * a i ≤ b i) ∧
      (∑ i ∈ F \ H, a i) ≤ (F.sum (fun i : I => a i - b i)) / θ := by
  classical
  let H := F.filter fun i => (1 - θ) * a i ≤ b i
  have hsub : H ⊆ F := Finset.filter_subset _ _
  have hfloor : ∀ i ∈ H, (1 - θ) * a i ≤ b i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hgap (i : I) (hi : i ∈ F \ H) : θ * a i ≤ a i - b i := by
    have hnot : ¬ (1 - θ) * a i ≤ b i := by
      intro h
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, h⟩)
    have hlt := lt_of_not_ge hnot
    nlinarith
  refine ⟨H, hsub, hfloor, ?_⟩
  apply (le_div_iff₀ hθ).mpr
  calc
    _ = ∑ i ∈ F \ H, θ * a i := by rw [← Finset.mul_sum]; ring
    _ ≤ (F \ H).sum (fun i : I => a i - b i) := Finset.sum_le_sum hgap
    _ ≤ F.sum (fun i : I => a i - b i) := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i hi _ => sub_nonneg.mpr (hba i hi))

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
