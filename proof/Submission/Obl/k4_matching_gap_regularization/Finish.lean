import Submission.Obl.k4_matching_gap_regularization.Sequence
import Submission.Obl.k4_matching_gap_regularization.Compactness

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open Filter
open scoped Topology

lemma fixed_exponents {D J : ℕ} (hDJ : D ≤ J) {d : ℝ}
    (hseq : ∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad D J d (1 / ((k : ℝ) + 1)) (N k)) :
    ∃ β : ℕ → ℝ, Admissible D J β ∧
      ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ Gap J d β ε N := by
  obtain ⟨b, N, hdata⟩ := regularizations_sequence hDJ hseq
  obtain ⟨β, φ, hβ, hφ, hlim⟩ := compact_exponent_subseq hDJ b (fun m => (hdata m).1)
  refine ⟨β, hβ, ?_⟩
  intro ε hε R hR
  have hthird : (0 : ℝ) < ε / 3 := by positivity
  have hclose : ∀ᶠ m : ℕ in atTop, ∀ j : Fin (J + 1), 1 ≤ j.val →
      |b (φ m) j.val - β j.val| ≤ ε / 3 := by
    apply eventually_all.2
    intro j
    by_cases hj : 1 ≤ j.val
    · have h := (hlim j.val hj (by omega)).eventually (Metric.ball_mem_nhds _ hthird)
      exact h.mono fun m hm _ => (show |b (φ m) j.val - β j.val| < ε / 3 by
        simpa only [Metric.mem_ball, Real.dist_eq] using hm).le
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  have hcut : ∀ᶠ m : ℕ in atTop, ∀ j : Fin (J + 1), 1 ≤ j.val →
      β j.val < 2 → b (φ m) j.val < 2 := by
    apply eventually_all.2
    intro j
    by_cases hj : 1 ≤ j.val
    · by_cases hb : β j.val < 2
      · exact ((hlim j.val hj (by omega)).eventually (gt_mem_nhds hb)).mono fun _ hm _ _ => hm
      · exact Eventually.of_forall fun _ _ h => False.elim (hb h)
    · exact Eventually.of_forall fun _ h _ => False.elim (hj h)
  have herr : Tendsto (fun m => 2 / ((φ m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero, mul_one_div] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).comp hφ.tendsto_atTop
  have het : ∀ᶠ m : ℕ in atTop, 2 / ((φ m : ℝ) + 1) ≤ ε / 3 :=
    (herr.eventually (gt_mem_nhds hthird)).mono fun _ hm => hm.le
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun m => (hdata m).2.1)
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hbig : ∀ᶠ m : ℕ in atTop, R ≤ N (φ m) :=
    (hNt.comp hφ.tendsto_atTop).eventually_ge_atTop R
  obtain ⟨m, hmclose, hmcut, hmeta, hmR⟩ := (hclose.and (hcut.and (het.and hbig))).exists
  refine ⟨N (φ m), hmR, ?_⟩
  apply gap_transport (η := 2 / ((φ m : ℝ) + 1)) (ε := ε) (β := b (φ m))
    (by linarith only [hR, hmR]) (by linarith only [hmeta, hε])
  · intro j hj₁ hjJ
    exact (hmclose ⟨j, by omega⟩ hj₁).trans (by linarith only [hmeta, hε])
  · intro j hj₁ hjJ hjcut
    exact hmcut ⟨j, by omega⟩ hj₁ hjcut
  · exact (hdata (φ m)).2.2

end Submission.Obl.k4_matching_gap_regularization
