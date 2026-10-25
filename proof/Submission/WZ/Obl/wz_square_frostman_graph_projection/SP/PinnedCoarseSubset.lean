-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PinnedCoarseSubset.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealCoarseSubset

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

theorem real_covering_subset_card (A B : Finset ℝ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hcov : ∀ a ∈ A, ∃ b ∈ B, dist a b ≤ ρ) :
    (A.card : ℝ) ≤ (2 * ρ / δ + 2) * (B.card : ℝ) := by
  classical
  let F (b : ℝ) := A.filter (fun a => dist a b ≤ ρ)
  have hsub : A ⊆ B.biUnion F := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
  have hcount (b : ℝ) : ((F b).card : ℝ) ≤ 2 * ρ / δ + 2 := by
    have hh := real_separated_ball_card hδ hρ (F b)
      (fun a ha c hc hne => hsep a (Finset.mem_filter.mp ha).1 c (Finset.mem_filter.mp hc).1 hne)
      (fun a ha => (Finset.mem_filter.mp ha).2)
    have hh' := (le_div_iff₀ hδ).mpr hh
    convert hh' using 1 <;> field_simp
  calc
    (A.card : ℝ) ≤ ((B.biUnion F).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ b ∈ B, ((F b).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ b ∈ B, (2 * ρ / δ + 2) := Finset.sum_le_sum (fun b hb => hcount b)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A prescribed point can be retained when passing to a coarser net. -/
theorem real_pinned_coarse_subset (A : Finset ℝ) {δ ρ p : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hp : p ∈ A) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    ∃ B : Finset ℝ, B ⊆ A ∧ p ∈ B ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → ρ ≤ dist a b) ∧
      (A.card : ℝ) ≤ (2 * ρ / δ + 2) * (B.card : ℝ) := by
  classical
  let U := A.filter (fun a => ρ ≤ dist a p)
  obtain ⟨n, cc, hcU, hccsep, hcov⟩ := exists_separated_cover U.finite_toSet.totallyBounded hρ
  let B := insert p (Finset.univ.image cc)
  have hBA : B ⊆ A := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hp
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact (Finset.mem_filter.mp (hcU i)).1
  have hBp : p ∈ B := Finset.mem_insert_self _ _
  have hBsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → ρ ≤ dist a b := by
    intro a ha b hb hne
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hne rfl).elim
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        simpa only [dist_comm] using (Finset.mem_filter.mp (hcU i)).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (Finset.mem_filter.mp (hcU i)).2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact (hccsep i j (fun hij => hne (hij ▸ rfl))).le
  have hcover : ∀ a ∈ A, ∃ b ∈ B, dist a b ≤ ρ := by
    intro a ha
    by_cases hfar : ρ ≤ dist a p
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (Finset.mem_filter.mpr ⟨ha, hfar⟩))
      exact ⟨cc i, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), hi⟩
    · exact ⟨p, hBp, (lt_of_not_ge hfar).le⟩
  exact ⟨B, hBA, hBp, hBsep, real_covering_subset_card A B hδ hρ.le hsep hcover⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
