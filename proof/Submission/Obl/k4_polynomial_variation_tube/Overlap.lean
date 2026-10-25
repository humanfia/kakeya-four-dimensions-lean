import Mathlib
import ChallengeDeps
open MeasureTheory Set

namespace Submission.Obl.k4_polynomial_variation_tube

open scoped Classical

lemma lattice_separated {n m : ℕ} (z : Fin m → Fin n → ℤ)
    (hz : Function.Injective z) {q r : Fin m} (hqr : q ≠ r) :
    1 ≤ dist (WithLp.toLp 2 (fun j => (z q j : ℝ)))
      (WithLp.toLp 2 (fun j => (z r j : ℝ))) := by
  have hne : z q ≠ z r := fun h => hqr (hz h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hi : (1 : ℤ) ≤ |z q j - z r j| := Int.one_le_abs (sub_ne_zero.mpr hj)
  have hr : (1 : ℝ) ≤ |(z q j : ℝ) - (z r j : ℝ)| := by exact_mod_cast hi
  exact hr.trans (by simpa [dist_eq_norm, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (z q j : ℝ)) -
      WithLp.toLp 2 (fun j => (z r j : ℝ))) j))

lemma exists_overlap_bound (n : ℕ) : ∃ N : ℕ, 0 < N ∧
    ∀ (m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin n)),
      (∀ q r, q ≠ r → 1 ≤ dist (c q) (c r)) →
      ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.ball (c q) 1)).card ≤ N := by
  classical
  obtain ⟨t, hts, ht⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).elim_nhds_subcover
    (fun x => Metric.ball x (1/2)) (fun x _ => Metric.ball_mem_nhds x (by norm_num))
  refine ⟨t.card + 1, by omega, ?_⟩
  intro m c hc x
  let s := Finset.univ.filter (fun q => x ∈ Metric.ball (c q) 1)
  have hcover : ∀ q : s, ∃ a : t, dist (c q - x) a < 1/2 := by
    intro q
    have hq : c q - x ∈ Metric.closedBall 0 1 := by
      have h := (Finset.mem_filter.mp q.property).2
      simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm,
        dist_comm] using (Metric.mem_ball.mp h).le
    obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact ⟨⟨a, ha⟩, hqa⟩
  choose a ha using hcover
  have hinj : Function.Injective a := by
    intro q r h
    apply Subtype.ext
    by_contra hqr
    have hdist := hc q r hqr
    have htriangle := dist_triangle (c q - x) (a q) (c r - x)
    have hq := ha q
    have hr := ha r
    rw [h] at hq
    rw [h, dist_sub_right, dist_comm (a r : EuclideanSpace ℝ (Fin n))] at htriangle
    linarith
  have hcard := Fintype.card_le_of_injective a hinj
  simp only [Fintype.card_coe] at hcard
  exact hcard.trans (Nat.le_add_right _ _)

end Submission.Obl.k4_polynomial_variation_tube
