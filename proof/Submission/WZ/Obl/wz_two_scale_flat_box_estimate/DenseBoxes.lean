-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.DenseBoxes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BalancedAssignments
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open Set

/-- A positive fraction of retained fine indices yields boxes with uniformly
many retained indices, while preserving a quantitative total-count bound. -/
lemma select_dense_assigned_boxes {n m L : ℕ} (hL : 0 < L)
    (f : Fin n → Fin L) (j : Fin m → Fin n) (hj : Function.Injective j)
    {F D θ : ℝ} (hF : 0 < F) (hD : 0 < D) (hθ : 0 < θ)
    (hlower : ∀ k, F ≤ (Set.ncard {i | f i = k} : ℝ))
    (hupper : ∀ k, (Set.ncard {i | f i = k} : ℝ) ≤ D * F)
    (hret : θ * n ≤ m) :
    ∃ (q : ℕ) (g : Fin q → Fin L), 0 < q ∧ Function.Injective g ∧
      θ * n ≤ 2 * D ^ 2 * q * F ∧
      ∀ k, θ / 2 * F ≤ (Set.ncard {i | f (j i) = g k} : ℝ) := by
  have hsum : ∑ k, (Set.ncard {i | f i = k} : ℝ) = n := by exact_mod_cast fiber_card_sum f
  have hsum' : ∑ k, (Set.ncard {i | f (j i) = k} : ℝ) = m := by
    exact_mod_cast fiber_card_sum (f ∘ j)
  have hlow : (L : ℝ) * F ≤ n := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hlower k)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] using hh
  have hhigh : (n : ℝ) ≤ L * (D * F) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hupper k)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] using hh
  have hu (k : Fin L) : (Set.ncard {i | f (j i) = k} : ℝ) ≤ D * F :=
    (Nat.cast_le.mpr (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily j hj
      (fun i => f i = k))).trans (hupper k)
  have hmass : 2 * (L : ℝ) * (θ / 2 * F) ≤ ∑ k, (Set.ncard {i | f (j i) = k} : ℝ) := by
    rw [hsum']
    have hh := mul_le_mul_of_nonneg_left hlow hθ.le
    nlinarith
  obtain ⟨q, g, hq, hg, hsize, hind⟩ :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.dense_index_subfamily hL
      (fun k => (Set.ncard {i | f (j i) = k} : ℝ)) (by positivity : 0 < θ / 2 * F)
      (mul_pos hD hF) hu hmass
  refine ⟨q, g, hq, hg, ?_, hind⟩
  have he : (θ / 2 * F) / (D * F) = θ / (2 * D) := by field_simp
  rw [he, div_mul_eq_mul_div] at hsize
  have hs := (div_le_iff₀ (by positivity : 0 < 2 * D)).mp hsize
  calc
    _ ≤ θ * (L * (D * F)) := mul_le_mul_of_nonneg_left hhigh hθ.le
    _ = (θ * L) * (D * F) := by ring
    _ ≤ ((q : ℝ) * (2 * D)) * (D * F) := mul_le_mul_of_nonneg_right hs (mul_pos hD hF).le
    _ = _ := by ring

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
