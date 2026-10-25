/-
Adapted from: here:o116
Original proofs by session x0394, o116 branch x0394, commit be640a0.
Source: Submission/Obl/k4_isotropic_residual_candidates/IteratedSymm.lean.
This helper has not entered lib.
-/
import Mathlib

/-!
# Symmetry of iterated derivatives of `C^n` functions

Mathlib proves the symmetry of `iteratedFDeriv` for analytic functions and the symmetry of the
second derivative of a `C^2` function. Here the symmetry of every iterated derivative of a
`C^n` function on an open set follows by induction. Adjacent slots are swapped either through
the first-slot recursion (`iteratedFDeriv_succ_apply_left`) or the last-slot recursion
(`iteratedFDeriv_succ_apply_right`), and swaps generate the symmetric group.
-/

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

open Equiv

universe u

/-- Invariance of a multilinear map under all permutations follows from invariance under swaps. -/
lemma comp_perm_eq_of_swaps {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (hswap : ∀ (i j : Fin k) (v : Fin k → E), T (v ∘ swap i j) = T v)
    (v : Fin k → E) (σ : Perm (Fin k)) : T (v ∘ σ) = T v := by
  let H : Subgroup (Perm (Fin k)) :=
    { carrier := {σ | ∀ v : Fin k → E, T (v ∘ σ) = T v}
      mul_mem' := by
        intro σ τ hσ hτ v
        have h1 : v ∘ ⇑(σ * τ) = (v ∘ σ) ∘ τ := rfl
        rw [h1, hτ (v ∘ σ), hσ v]
      one_mem' := by
        intro v
        rfl
      inv_mem' := by
        intro σ hσ v
        have h1 := hσ (v ∘ ⇑σ⁻¹)
        have h2 : (v ∘ ⇑σ⁻¹) ∘ ⇑σ = v := by
          funext x
          simp
        rw [h2] at h1
        exact h1.symm }
  have hcl : Subgroup.closure {σ : Perm (Fin k) | σ.IsSwap} ≤ H := by
    rw [Subgroup.closure_le]
    rintro σ ⟨i, j, -, rfl⟩ v
    exact hswap i j v
  rw [Equiv.Perm.closure_isSwap] at hcl
  exact hcl (Subgroup.mem_top σ) v

section Slots

variable {E : Type*}

lemma tail_comp_swap_succ {n : ℕ} (v : Fin (n + 1) → E) (a b : Fin n) :
    Fin.tail (v ∘ swap a.succ b.succ) = Fin.tail v ∘ swap a b := by
  funext i
  simp only [Fin.tail, Function.comp_apply]
  congr 1
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all [Fin.succ_inj]

lemma comp_swap_succ_zero {n : ℕ} (v : Fin (n + 1) → E) (a b : Fin n) :
    (v ∘ swap a.succ b.succ) 0 = v 0 := by
  simp only [Function.comp_apply]
  rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]

lemma init_comp_swap_castSucc {n : ℕ} (v : Fin (n + 1) → E) (a b : Fin n) :
    Fin.init (v ∘ swap a.castSucc b.castSucc) = Fin.init v ∘ swap a b := by
  funext i
  simp only [Fin.init, Function.comp_apply]
  congr 1
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all [Fin.castSucc_inj]

lemma comp_swap_castSucc_last {n : ℕ} (v : Fin (n + 1) → E) (a b : Fin n) :
    (v ∘ swap a.castSucc b.castSucc) (Fin.last n) = v (Fin.last n) := by
  simp only [Function.comp_apply]
  rw [swap_apply_of_ne_of_ne (Fin.castSucc_lt_last a).ne' (Fin.castSucc_lt_last b).ne']

end Slots

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First-slot recursion: symmetry of `D^n f` near `x` gives invariance of `D^(n+1) f x`
under swaps of two slots other than the first. -/
lemma iteratedFDeriv_succ_swap_succ {n : ℕ} {f : E → F} {x : E}
    (hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x)
    (hsymm : ∀ᶠ y in nhds x, ∀ (w : Fin n → E) (a b : Fin n),
      iteratedFDeriv ℝ n f y (w ∘ swap a b) = iteratedFDeriv ℝ n f y w)
    (a b : Fin n) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ swap a.succ b.succ) = iteratedFDeriv ℝ (n + 1) f x v := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left,
    comp_swap_succ_zero, tail_comp_swap_succ]
  set w := Fin.tail v
  -- the two evaluation functions agree near `x`
  have hev : (fun y => iteratedFDeriv ℝ n f y (w ∘ swap a b)) =ᶠ[nhds x]
      (fun y => iteratedFDeriv ℝ n f y w) := by
    filter_upwards [hsymm] with y hy using hy w a b
  have h1 := hev.fderiv_eq (𝕜 := ℝ)
  have happ : ∀ u : Fin n → E, fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F u).comp
        (fderiv ℝ (iteratedFDeriv ℝ n f) x) := by
    intro u
    have : (fun y => iteratedFDeriv ℝ n f y u) =
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F u) ∘ iteratedFDeriv ℝ n f := rfl
    rw [this, fderiv_comp x (ContinuousLinearMap.differentiableAt _) hdiff,
      ContinuousLinearMap.fderiv]
  rw [happ, happ] at h1
  have h2 := congrArg (fun L => L (v 0)) h1
  simpa using h2

/-- Last-slot recursion: symmetry of `D^n (Df) x` gives invariance of `D^(n+1) f x` under
swaps of two slots other than the last. -/
lemma iteratedFDeriv_succ_swap_castSucc {n : ℕ} {f : E → F} {x : E}
    (hsymm : ∀ (w : Fin n → E) (a b : Fin n),
      iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x (w ∘ swap a b) =
        iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x w)
    (a b : Fin n) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ swap a.castSucc b.castSucc) =
      iteratedFDeriv ℝ (n + 1) f x v := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right,
    comp_swap_castSucc_last, init_comp_swap_castSucc, hsymm]



theorem iteratedFDeriv_swap_of_contDiffOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E}, IsOpen U →
      ∀ {f : E → F}, ContDiffOn ℝ n f U → ∀ x ∈ U, ∀ (v : Fin n → E) (a b : Fin n),
        iteratedFDeriv ℝ n f x (v ∘ swap a b) = iteratedFDeriv ℝ n f x v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ _ U hU f hf x hx v a b
  rcases eq_or_ne a b with rfl | hab
  · simp
  match n, ih, hf, v, a, b, hab with
  | 0, _, _, _, a, _, _ => exact a.elim0
  | 1, _, _, _, a, b, hab => exact absurd (Subsingleton.elim a b) hab
  | 2, _, hf, v, a, b, hab =>
    have hx' : ContDiffAt ℝ 2 f x := hf.contDiffAt (hU.mem_nhds hx)
    have hsym := hx'.isSymmSndFDerivAt (by simp)
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    have hsw : v ∘ swap a b = ![v 1, v 0] := by
      funext i
      fin_cases a <;> fin_cases b <;> simp at hab <;> fin_cases i <;> simp
    rw [hsw, IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hsym), ← hv]
  | n + 3, ih, hf, v, a, b, hab =>
    -- `f` is `C^(n+2)` on `U`, so `D^(n+2) f` is swap-invariant on `U`
    have hfn : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U :=
      hf.of_le (by exact_mod_cast (by omega : n + 2 ≤ n + 3))
    have hleft : ∀ (a' b' : Fin (n + 2)) (w : Fin (n + 3) → E),
        iteratedFDeriv ℝ (n + 3) f x (w ∘ swap a'.succ b'.succ) =
          iteratedFDeriv ℝ (n + 3) f x w := by
      intro a' b' w
      have hxat : ContDiffAt ℝ ((n + 3 : ℕ) : WithTop ℕ∞) f x := hf.contDiffAt (hU.mem_nhds hx)
      refine iteratedFDeriv_succ_swap_succ
        (hxat.differentiableAt_iteratedFDeriv (by exact_mod_cast (by omega : n + 2 < n + 3))) ?_ a' b' w
      filter_upwards [hU.mem_nhds hx] with y hy w' c d
      exact ih (n + 2) (by omega) hU hfn y hy w' c d
    have hright : ∀ (a' b' : Fin (n + 2)) (w : Fin (n + 3) → E),
        iteratedFDeriv ℝ (n + 3) f x (w ∘ swap a'.castSucc b'.castSucc) =
          iteratedFDeriv ℝ (n + 3) f x w := by
      intro a' b' w
      have hdf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ f y) U :=
        hf.fderiv_of_isOpen hU (by norm_cast)
      exact iteratedFDeriv_succ_swap_castSucc (fun w' c d => ih (n + 2) (by omega) hU hdf x hx w' c d)
        a' b' w
    -- a swap avoiding `0` or avoiding the last slot is handled directly
    have hgood : ∀ (c d : Fin (n + 3)), (c ≠ 0 ∧ d ≠ 0) ∨ (c ≠ Fin.last (n + 2) ∧ d ≠ Fin.last (n + 2)) →
        ∀ w : Fin (n + 3) → E,
          iteratedFDeriv ℝ (n + 3) f x (w ∘ swap c d) = iteratedFDeriv ℝ (n + 3) f x w := by
      intro c d hcd w
      rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
      · obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc
        obtain ⟨d', rfl⟩ := Fin.exists_succ_eq.mpr hd
        exact hleft c' d' w
      · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.mpr hc
        obtain ⟨d', rfl⟩ := Fin.exists_castSucc_eq.mpr hd
        exact hright c' d' w
    by_cases h : (a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ Fin.last (n + 2) ∧ b ≠ Fin.last (n + 2))
    · exact hgood a b h v
    · -- `{a, b} = {0, last}`: conjugate by the swap of `0` and `1`
      have h1 : (1 : Fin (n + 3)) ≠ 0 := by simp
      have h1l : (1 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
        rw [Ne, Fin.ext_iff]; simp [Fin.val_last]
      have h0l : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
        rw [Ne, Fin.ext_iff]; simp [Fin.val_last]
      have hab' : swap a b = swap 0 (Fin.last (n + 2)) := by
        push Not at h
        by_cases ha : a = 0
        · subst ha
          have hb : b = Fin.last (n + 2) := by
            by_contra hb
            exact absurd (h.2 h0l) hb
          rw [hb]
        · have hb : b = 0 := by
            by_contra hb
            exact absurd (h.1 ha) hb
          have ha' : a = Fin.last (n + 2) := by
            by_contra ha'
            exact absurd (h.2 ha') (by rw [hb]; exact h0l)
          rw [ha', hb, swap_comm]
      have hconj : swap (1 : Fin (n + 3)) 0 * swap (Fin.last (n + 2)) 1 * swap 1 0 =
          swap 0 (Fin.last (n + 2)) :=
        swap_mul_swap_mul_swap h1l.symm h0l.symm
      rw [hab', ← hconj]
      have e : v ∘ ⇑((swap (1 : Fin (n + 3)) 0 * swap (Fin.last (n + 2)) 1 * swap 1 0 :
          Perm (Fin (n + 3)))) =
          ((v ∘ swap (1 : Fin (n + 3)) 0) ∘ swap (Fin.last (n + 2)) 1) ∘ swap 1 0 := rfl
      rw [e, hgood 1 0 (Or.inr ⟨h1l, h0l⟩), hgood (Fin.last (n + 2)) 1 (Or.inl ⟨h0l.symm, h1⟩),
        hgood 1 0 (Or.inr ⟨h1l, h0l⟩)]

/-- The iterated derivative of a `C^n` function on an open set is symmetric. -/
theorem iteratedFDeriv_comp_perm_of_contDiffOn {E F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f U) {x : E} (hx : x ∈ U) (v : Fin n → E)
    (σ : Perm (Fin n)) : iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v :=
  comp_perm_eq_of_swaps _ (fun i j w => iteratedFDeriv_swap_of_contDiffOn n hU hf x hx w i j) v σ

end Submission.Obl.k4_seven_direction_third_derivative_bound
