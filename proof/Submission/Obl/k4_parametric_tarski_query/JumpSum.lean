import Mathlib

/-!
Adapted from the same LOT tree, obligation o050, session x0159,
commit f99d6af7e8420c51ce38439aeede86aba6326413, file `Submission/Obl/k4_sign_projection/JumpSum.lean`.
The declarations and imports have been moved to this obligation's namespace.
-/

namespace Submission.Obl.k4_parametric_tarski_query

open Filter
open scoped Topology BigOperators

/-- A step with its value at the jump chosen on the right. -/
noncomputable def jumpStep (a : ℝ) (d : ℤ) (x : ℝ) : ℤ := if a ≤ x then d else 0

theorem eventually_jumpStep_right (a y : ℝ) (d : ℤ) :
    ∀ᶠ x in 𝓝[>] y, jumpStep a d x = jumpStep a d y := by
  by_cases h : a ≤ y
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp [jumpStep, h, h.trans hx.le]
  · have hy : y < a := lt_of_not_ge h
    filter_upwards [(eventually_lt_nhds hy).filter_mono nhdsWithin_le_nhds] with x hx
    simp [jumpStep, h, hx.not_ge]

theorem eventually_jumpStep_left (a y : ℝ) (d : ℤ) :
    ∀ᶠ x in 𝓝[<] y, jumpStep a d x = if a < y then d else 0 := by
  by_cases h : a < y
  · filter_upwards [(eventually_gt_nhds h).filter_mono nhdsWithin_le_nhds] with x hx
    simp [jumpStep, h, hx.le]
  · have hy : y ≤ a := le_of_not_gt h
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [jumpStep, h, (hx.trans_le hy).not_ge]

theorem eventually_jumpStep_top (a : ℝ) (d : ℤ) :
    ∀ᶠ x in atTop, jumpStep a d x = d := by
  filter_upwards [eventually_ge_atTop a] with x hx
  simp [jumpStep, hx]

theorem eventually_jumpStep_bot (a : ℝ) (d : ℤ) :
    ∀ᶠ x in atBot, jumpStep a d x = 0 := by
  filter_upwards [eventually_lt_atBot a] with x hx
  simp [jumpStep, hx.not_ge]

noncomputable def jumpCorrection (s : Finset ℝ) (d : ℝ → ℤ) (x : ℝ) : ℤ :=
  ∑ a ∈ s, jumpStep a (d a) x

theorem jumpCorrection_eq (s : Finset ℝ) (d : ℝ → ℤ) (y : ℝ) :
    jumpCorrection s d y = (∑ a ∈ s, if a < y then d a else 0) +
      if y ∈ s then d y else 0 := by
  classical
  have hterm (a : ℝ) : jumpStep a (d a) y =
      (if a < y then d a else 0) + (if a = y then d a else 0) := by
    rcases lt_trichotomy a y with h | rfl | h
    · simp [jumpStep, h, h.le, h.ne]
    · simp [jumpStep]
    · simp [jumpStep, h.not_ge, h.not_gt, h.ne']
  simp only [jumpCorrection, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem eventually_jumpCorrection_right (s : Finset ℝ) (d : ℝ → ℤ) (y : ℝ) :
    ∀ᶠ x in 𝓝[>] y, jumpCorrection s d x = jumpCorrection s d y := by
  have h := s.eventually_all.mpr (fun a _ => eventually_jumpStep_right a y (d a))
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl hx

theorem eventually_jumpCorrection_left (s : Finset ℝ) (d : ℝ → ℤ) (y : ℝ) :
    ∀ᶠ x in 𝓝[<] y, jumpCorrection s d x = ∑ a ∈ s, if a < y then d a else 0 := by
  have h := s.eventually_all.mpr (fun a _ => eventually_jumpStep_left a y (d a))
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl hx

theorem eventually_jumpCorrection_top (s : Finset ℝ) (d : ℝ → ℤ) :
    ∀ᶠ x in atTop, jumpCorrection s d x = ∑ a ∈ s, d a := by
  have h := s.eventually_all.mpr (fun a _ => eventually_jumpStep_top a (d a))
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl hx

theorem eventually_jumpCorrection_bot (s : Finset ℝ) (d : ℝ → ℤ) :
    ∀ᶠ x in atBot, jumpCorrection s d x = 0 := by
  have h := s.eventually_all.mpr (fun a _ => eventually_jumpStep_bot a (d a))
  filter_upwards [h] with x hx
  change ∑ a ∈ s, jumpStep a (d a) x = 0
  exact Finset.sum_eq_zero hx

/-- The total of finitely many jumps is the difference between the values at infinity. -/
theorem sum_jumps_eq (s : Finset ℝ) (f l : ℝ → ℤ) (t b : ℤ)
    (hr : ∀ a, ∀ᶠ x in 𝓝[>] a, f x = f a)
    (hl : ∀ a, ∀ᶠ x in 𝓝[<] a, f x = l a)
    (hs : ∀ a, a ∉ s → f a = l a)
    (ht : ∀ᶠ x in atTop, f x = t)
    (hb : ∀ᶠ x in atBot, f x = b) :
    ∑ a ∈ s, (f a - l a) = t - b := by
  classical
  let d := fun a => f a - l a
  let g := fun x => f x - jumpCorrection s d x
  have hg : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).mpr
    intro y
    have hright : ∀ᶠ x in 𝓝[>] y, g x = g y := by
      filter_upwards [hr y, eventually_jumpCorrection_right s d y] with x hx hcorr
      simp only [g, hx, hcorr]
    have hleft : ∀ᶠ x in 𝓝[<] y, g x = g y := by
      have hcorr := jumpCorrection_eq s d y
      have hd : (if y ∈ s then d y else 0) = f y - l y := by
        by_cases hy : y ∈ s
        · simp [hy, d]
        · simp [hy, hs y hy]
      rw [hd] at hcorr
      filter_upwards [hl y, eventually_jumpCorrection_left s d y] with x hx hcx
      dsimp only [g]
      rw [hx, hcx]
      omega
    rw [← nhdsLT_sup_nhdsGE y, eventually_sup]
    refine ⟨hleft, ?_⟩
    rw [← nhdsGT_sup_nhdsWithin_singleton y, eventually_sup]
    refine ⟨hright, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxy : x = y := hx
    subst x
    rfl
  obtain ⟨x, hx, hcx⟩ := (ht.and (eventually_jumpCorrection_top s d)).exists
  obtain ⟨y, hy, hcy⟩ := (hb.and (eventually_jumpCorrection_bot s d)).exists
  have hxy := hg.apply_eq_of_preconnectedSpace x y
  dsimp only [g] at hxy
  rw [hx, hcx, hy, hcy] at hxy
  change (∑ a ∈ s, d a) = t - b
  omega

end Submission.Obl.k4_parametric_tarski_query
