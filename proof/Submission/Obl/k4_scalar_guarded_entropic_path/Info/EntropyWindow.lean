/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/EntropyWindow.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
/-
Adapted from this LOT tree, o134, session x0438, branch x0438,
file Submission/Obl/k4_scalar_guarded_tangent_obstruction/EntropyWindow.lean.
The reference-law and palette constructions retain their original denominators.
-/

import Submission.Obl.k4_matching_palette_likelihood

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

/-- Choose the entropy window using the fixed original path probability
and its finest requested velocity palette, before later restrictions. -/
theorem exists_low_information_window
    (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ)
    (hL : 0 < L) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter
      (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) :
    ∃ a : ℕ, a < L ∧
      (∑ x, p x * max 0 (Real.log
        (posterior p (F (a + C)) Z x / posterior p (F a) Z x))) ≤
      (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + 1 := by
  classical
  have hsum := Submission.k4_matching_palette_likelihood n L C M p F Z
    hC hM hp hp1 hnest hsupp
  change (∑ a ∈ Finset.range L, ∑ x, p x * max 0 (Real.log
    (posterior p (F (a + C)) Z x / posterior p (F a) Z x))) ≤
    (C : ℝ) * Real.log (M : ℝ) + L at hsum
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  by_contra! hbad
  have hnonempty : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr hL⟩
  have hstrict := Finset.sum_lt_sum_of_nonempty hnonempty
    (fun a ha => hbad a (Finset.mem_range.mp ha))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstrict
  have hident : (L : ℝ) * ((C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + 1) =
      (C : ℝ) * Real.log (M : ℝ) + L := by
    field_simp [hLreal.ne']
  linarith only [hstrict, hsum, hident]

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
