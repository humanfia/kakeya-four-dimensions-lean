-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open Metric

/-- A uniform finite cover converts the local coefficient count to a global count. -/
theorem coefficient_card_bound : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {δ η : ℝ},
      0 < δ → δ ≤ 1 → (∀ i, ‖q i‖ ≤ 10) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) →
      (n : ℝ) ≤ C * (δ ^ (-η) / δ) := by
  classical
  obtain ⟨centers, hcover⟩ := (isCompact_closedBall
    (0 : EuclideanSpace ℝ (Fin 3)) 10).elim_finite_subcover
      (fun x => ball x 1) (fun _ => isOpen_ball) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨x, mem_ball_self (by norm_num)⟩)
  refine ⟨(centers.card : ℝ) + 1, by positivity, ?_⟩
  intro n q δ η hδ hδ1 hq hcount
  let fibers : EuclideanSpace ℝ (Fin 3) → Finset (Fin n) :=
    fun x => Finset.univ.filter (fun i => q i ∈ ball x 1)
  have hcovered : (Finset.univ : Finset (Fin n)) ⊆ centers.biUnion fibers := by
    intro i hi
    have hqi : q i ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 10 := by
      simpa using hq i
    obtain ⟨x, hx, hix⟩ := Set.mem_iUnion₂.mp (hcover hqi)
    exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa [fibers] using hix⟩
  have hn : (n : ℝ) ≤ ∑ x ∈ centers, ((fibers x).card : ℝ) := by
    have h := (Finset.card_le_card hcovered).trans Finset.card_biUnion_le
    simpa using (Nat.cast_le (α := ℝ)).mpr h
  calc
    (n : ℝ) ≤ ∑ x ∈ centers, ((fibers x).card : ℝ) := hn
    _ ≤ ∑ _x ∈ centers, δ ^ (-η) / δ := by
      apply Finset.sum_le_sum
      intro x hx
      have hfiber : (↑(fibers x) : Set (Fin n)) = {i | q i ∈ ball x 1} := by
        ext i
        simp [fibers]
      have h := hcount x 1 hδ1 le_rfl
      rw [← hfiber, Set.ncard_coe_finset] at h
      simpa [div_eq_mul_inv] using h
    _ = (centers.card : ℝ) * (δ ^ (-η) / δ) := by simp
    _ ≤ ((centers.card : ℝ) + 1) * (δ ^ (-η) / δ) := by
      gcongr
      linarith

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
