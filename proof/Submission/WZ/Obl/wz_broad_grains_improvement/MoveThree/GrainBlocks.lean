-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainBlocks.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainBlocks.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClusterEnclosure
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Factoring

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (Upper)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)

noncomputable section

/-- Stable concentration of grains produces disjoint index blocks in
saturated prism containers of a common long length. -/
theorem grainCoefficient_dense_prism_blocks {L : ℕ} {a ρ c K : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (hK : 0 < K) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
    (Q : Finset (Fin L)) (hlarge : 2 * K < grainCoefficient a ρ c z e Q)
    (hstable : ∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
      grainCoefficient a ρ c z e Q ≤ K * grainCoefficient a ρ c z e R) :
    ∃ F : Finset (Finset (Fin L)),
      (∀ R ∈ F, R.Nonempty ∧ R ⊆ Q ∧
        ∃ (j i : Fin L) (A B : ℝ) (E : V ≃ₗᵢ[ℝ] V),
          j ∈ Q ∧ i ∈ R ∧ 0 < A ∧ A ≤ B ∧ B ≤ 10 * c ∧
          (∀ k ∈ R, grainNear a ρ c z e j k ∧
            P a (ρ * c) c (z k) (e k) ⊆ P A B (10 * c) (z i) E) ∧
          grainCoefficient a ρ c z e Q / (69120 * K) * (A * B * (10 * c)) <
            (R.card : ℝ) * (a * (ρ * c) * c) ∧
          Upper (fun k => P a (ρ * c) c (z k) (e k)) (a * (ρ * c) * c) R
            (grainCoefficient a ρ c z e Q) ∧
          Upper (fun k => P a (ρ * c) c (z k) (e k)) (A * B * (10 * c)) R
            (69120 * K * R.card)) ∧
      (↑F : Set (Finset (Fin L))).PairwiseDisjoint id ∧
      (Q.card : ℝ) ≤ 2 * (F.biUnion id).card := by
  classical
  obtain ⟨F, hF, hdisj, hcard⟩ := localCoefficient_dense_blocks
    (fun k => P a (ρ * c) c (z k) (e k)) (grainNear a ρ c z e) Q
    (by positivity : 0 < a * (ρ * c) * c) hK
    (fun k _ => (frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le (z k) (e k)).ge)
    hlarge hstable
  refine ⟨F, ?_, hdisj, hcard⟩
  intro R hR
  obtain ⟨hRne, hRQ, j, hj, W, hW, hfin, hcover, hden, hupper⟩ := hF R hR
  obtain ⟨A, B, i, E, hi, hA, hAB, hB, hbox, hvol⟩ := grain_block_enclosure
    ha hρ hρ1 hc hac z e R hRne j (fun k hk => (hcover k hk).1)
    hW hfin (fun k hk => (hcover k hk).2)
  refine ⟨hRne, hRQ, j, i, A, B, E, hj, hi, hA, hAB, hB,
    fun k hk => ⟨(hcover k hk).1, hbox k hk⟩, ?_⟩
  have hcoef : 0 ≤ grainCoefficient a ρ c z e Q := by linarith
  have heq : grainCoefficient a ρ c z e Q / (69120 * K) *
      (34560 * (μ W).toReal) =
      grainCoefficient a ρ c z e Q / (2 * K) * (μ W).toReal := by ring
  have hdense : grainCoefficient a ρ c z e Q / (69120 * K) *
      (A * B * (10 * c)) < (R.card : ℝ) * (a * (ρ * c) * c) := by
    calc
      _ ≤ grainCoefficient a ρ c z e Q / (69120 * K) * (34560 * (μ W).toReal) :=
        mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = _ := heq
      _ < _ := hden
  refine ⟨hdense, hupper, ?_⟩
  have hBpos : 0 < B := hA.trans_le hAB
  apply hupper.rescale (by positivity) (by positivity) hcoef (by positivity)
  have ht := (mul_le_mul_of_nonneg_left hdense.le (by positivity : 0 ≤ 69120 * K))
  have he : (69120 * K) *
      (grainCoefficient a ρ c z e Q / (69120 * K) * (A * B * (10 * c))) =
      grainCoefficient a ρ c z e Q * (A * B * (10 * c)) := by
    field_simp
  rw [he] at ht
  simpa only [grainCoefficient, mul_assoc] using ht

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
