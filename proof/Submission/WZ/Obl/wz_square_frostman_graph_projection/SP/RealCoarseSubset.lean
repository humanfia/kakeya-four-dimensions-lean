-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealCoarseSubset.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


/-- A real separated set has a coarser separated subset of controlled size. -/
theorem real_coarse_separated_subset (A : Finset ℝ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    ∃ B : Finset ℝ, B ⊆ A ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → ρ ≤ dist a b) ∧
      (A.card : ℝ) ≤ (2 * ρ / δ + 2) * (B.card : ℝ) := by
  classical
  obtain ⟨n, cc, hcA, hccsep, hcov⟩ := exists_separated_cover A.finite_toSet.totallyBounded hρ
  let B := Finset.univ.image cc
  have hinj : Function.Injective cc := by
    intro i j hij
    by_contra hne
    have hh := hccsep i j hne
    rw [hij, dist_self] at hh
    linarith
  have hBn : B.card = n := by
    rw [Finset.card_image_iff.mpr (fun i _ j _ hij => hinj hij)]
    simp
  have hBA : B ⊆ A := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hcA i
  have hBsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → ρ ≤ dist a b := by
    intro a ha b hb hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact (hccsep i j (fun hij => hne (hij ▸ rfl))).le
  have hcov' : Covers ρ ((fun x : ℝ => x) '' (↑A : Set ℝ)) cc := by simpa using hcov
  have hbound (j : Fin n) : ((A.filter (fun a => dist a (cc j) ≤ ρ)).card : ℝ) ≤ 2 * ρ / δ + 2 := by
    have hh := real_separated_ball_card hδ hρ.le (A.filter (fun a => dist a (cc j) ≤ ρ))
      (fun a ha b hb hne => hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hne)
      (fun a ha => (Finset.mem_filter.mp ha).2)
    have hh' := (le_div_iff₀ hδ).mpr hh
    convert hh' using 1 <;> field_simp <;> ring
  have hh := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound A (fun x : ℝ => x) hcov' hbound
  refine ⟨B, hBA, hBsep, ?_⟩
  rw [hBn]
  simpa only [mul_comm] using hh

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
