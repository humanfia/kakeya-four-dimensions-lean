import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set

/-- Repeated Rolle's theorem for an ordered list of zeros. -/
theorem exists_iteratedDeriv_eq_zero (q : ℕ) {f : ℝ → ℝ} {T : ℝ}
    (hT : T ≤ 1) (hf : ContDiffOn ℝ q f (Ioo (-2 : ℝ) 2))
    (a : Fin (q + 1) → ℝ) (ha : StrictMono a)
    (haI : ∀ i, a i ∈ Icc (0 : ℝ) T) (hzero : ∀ i, f (a i) = 0) :
    ∃ y ∈ Icc (0 : ℝ) T, iteratedDeriv q f y = 0 := by
  induction q generalizing f with
  | zero =>
    exact ⟨a 0, haI 0, by simpa only [iteratedDeriv_zero] using hzero 0⟩
  | succ q ih =>
    have hex (i : Fin (q + 1)) :
        ∃ y ∈ Ioo (a i.castSucc) (a i.succ), deriv f y = 0 := by
      apply exists_deriv_eq_zero (ha Fin.castSucc_lt_succ)
      · apply hf.continuousOn.mono
        intro t ht
        constructor <;> linarith [ht.1, ht.2, (haI i.castSucc).1, (haI i.succ).2]
      · rw [hzero, hzero]
    choose y hy hdy using hex
    have hymono : StrictMono y := by
      intro i j hij
      have hij' : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        exact hij
      exact (hy i).2.trans_le ((ha.monotone hij').trans (hy j).1.le)
    have hyI : ∀ i, y i ∈ Icc (0 : ℝ) T := by
      intro i
      exact ⟨(haI i.castSucc).1.trans (hy i).1.le,
        (hy i).2.le.trans (haI i.succ).2⟩
    have hdf : ContDiffOn ℝ q (deriv f) (Ioo (-2 : ℝ) 2) :=
      hf.deriv_of_isOpen isOpen_Ioo (by simp)
    obtain ⟨z, hz, hdz⟩ := ih hdf y hymono hyI hdy
    exact ⟨z, hz, by simpa only [iteratedDeriv_succ'] using hdz⟩

end Submission.Obl.k4_algebraic_sheet_remez
