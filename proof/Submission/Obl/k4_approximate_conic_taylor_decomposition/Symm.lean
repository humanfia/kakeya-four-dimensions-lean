/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/Symm.lean. -/
import Mathlib

/-!
# Symmetry of iterated derivatives

For a `C^N` function on an open set, every iterated derivative of order at most `N` is a
symmetric multilinear map. We also identify the first and second derivatives of a
directional test `v ↦ D^n g(v) w` with the full iterated derivative of `g`.
-/

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma differentiableAt_iteratedFDeriv_of_isOpen {N : WithTop ℕ∞} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {k : ℕ} (hk : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ N)
    {x : E} (hx : x ∈ U) : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x := by
  refine (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv ?_
  refine lt_of_lt_of_le ?_ hk
  exact_mod_cast Nat.lt_succ_self k

/-- The derivative of a directional test is the next iterated derivative. -/
lemma fderiv_iteratedFDeriv_apply_const {N : WithTop ℕ∞} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ N g U) {n : ℕ} (hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N)
    {x : E} (hx : x ∈ U) (w : Fin n → E) (y : E) :
    fderiv ℝ (fun v => iteratedFDeriv ℝ n g v w) x y =
      iteratedFDeriv ℝ (n + 1) g x (Fin.cons y w) := by
  rw [fderiv_continuousMultilinear_apply_const_apply
    (differentiableAt_iteratedFDeriv_of_isOpen hU hg hn hx), iteratedFDeriv_succ_apply_left]
  simp

lemma contDiffAt_two_apply_const {N : WithTop ℕ∞} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ N g U) {n : ℕ} (hn : ((n + 2 : ℕ) : WithTop ℕ∞) ≤ N)
    {x : E} (hx : x ∈ U) (w : Fin n → E) :
    ContDiffAt ℝ 2 (fun v => iteratedFDeriv ℝ n g v w) x := by
  have h2 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n g) x := by
    refine (hg.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right ?_
    refine le_trans (le_of_eq ?_) hn
    push_cast
    ring
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F w).contDiff.contDiffAt.comp x h2

/-- The second derivative of a directional test is the iterated derivative two orders up. -/
lemma iteratedFDeriv_two_iteratedFDeriv_apply_const {N : WithTop ℕ∞} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ N g U) {n : ℕ} (hn : ((n + 2 : ℕ) : WithTop ℕ∞) ≤ N)
    {x : E} (hx : x ∈ U) (w : Fin n → E) (y z : E) :
    iteratedFDeriv ℝ 2 (fun v => iteratedFDeriv ℝ n g v w) x ![y, z] =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons y (Fin.cons z w)) := by
  have hn1 : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N :=
    le_trans (by exact_mod_cast Nat.le_succ (n + 1)) hn
  have hc : DifferentiableAt ℝ (fderiv ℝ (fun v => iteratedFDeriv ℝ n g v w)) x :=
    ((contDiffAt_two_apply_const hU hg hn hx w).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : fderiv ℝ (fderiv ℝ (fun v => iteratedFDeriv ℝ n g v w)) x y z =
      fderiv ℝ (fun v => fderiv ℝ (fun v => iteratedFDeriv ℝ n g v w) v z) x y := by
    rw [fderiv_clm_apply hc (differentiableAt_const z)]
    simp
  rw [h1]
  have hev : (fun v => fderiv ℝ (fun v => iteratedFDeriv ℝ n g v w) v z) =ᶠ[nhds x]
      fun v => iteratedFDeriv ℝ (n + 1) g v (Fin.cons z w) := by
    filter_upwards [hU.mem_nhds hx] with v hv
    exact fderiv_iteratedFDeriv_apply_const hU hg hn1 hv w z
  rw [hev.fderiv_eq]
  exact fderiv_iteratedFDeriv_apply_const hU hg hn hx _ y

/-- Iterated derivatives of a `C^N` function on an open set are symmetric. -/
theorem iteratedFDeriv_comp_perm {N : WithTop ℕ∞} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ N f U) : ∀ (n : ℕ), (n : WithTop ℕ∞) ≤ N → ∀ x ∈ U,
      ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → E),
        iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m := by
  intro n
  induction n with
  | zero =>
    intro _ x _ σ m
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro hn x hx σ m
    cases n with
    | zero =>
      have : m ∘ σ = m := by
        funext i
        simp only [comp_apply]
        congr 1
        exact Fin.ext (by have := (σ i).isLt; have := i.isLt; omega)
      rw [this]
    | succ n =>
      have hn1 : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N :=
        le_trans (by exact_mod_cast Nat.le_succ (n + 1)) hn
      -- swaps of two tail positions
      have htail : ∀ (i j : Fin (n + 1)) (m : Fin (n + 2) → E),
          iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap i.succ j.succ) =
            iteratedFDeriv ℝ (n + 2) f x m := by
        intro i j m
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
          differentiableAt_iteratedFDeriv_of_isOpen hU hf hn hx
        have h0 : (m ∘ Equiv.swap i.succ j.succ) 0 = m 0 := by
          simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm]
        have ht : Fin.tail (m ∘ Equiv.swap i.succ j.succ) = Fin.tail m ∘ Equiv.swap i j := by
          funext k
          simp [Fin.tail, (Fin.succ_injective (n + 1)).swap_apply]
        change iteratedFDeriv ℝ ((n + 1) + 1) f x _ = iteratedFDeriv ℝ ((n + 1) + 1) f x m
        rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, h0, ht,
          ← fderiv_continuousMultilinear_apply_const_apply hdiff,
          ← fderiv_continuousMultilinear_apply_const_apply hdiff]
        congr 1
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hn1 y hy _ _
      -- the swap of the first two positions
      have h01 : ∀ m : Fin (n + 2) → E,
          iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (n + 2) f x m := by
        intro m
        set w : Fin n → E := Fin.tail (Fin.tail m)
        have hsymm : IsSymmSndFDerivAt ℝ (fun v => iteratedFDeriv ℝ n f v w) x :=
          (contDiffAt_two_apply_const hU hf hn hx w).isSymmSndFDerivAt (by simp)
        have hm : m = Fin.cons (m 0) (Fin.cons (m 1) w) := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rfl
          · refine Fin.cases ?_ (fun k => ?_) k
            · rfl
            · rfl
        have hms : m ∘ Equiv.swap 0 1 = Fin.cons (m 1) (Fin.cons (m 0) w) := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · simp
          · refine Fin.cases ?_ (fun k => ?_) k
            · simp
            · have h1 : (k.succ.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
              have h2 : (k.succ.succ : Fin (n + 2)) ≠ 1 := fun h =>
                Fin.succ_ne_zero k (Fin.succ_injective _ h)
              simp [Equiv.swap_apply_of_ne_of_ne h1 h2, w, Fin.tail]
        rw [hms, ← iteratedFDeriv_two_iteratedFDeriv_apply_const hU hf hn hx]
        conv_rhs => rw [hm, ← iteratedFDeriv_two_iteratedFDeriv_apply_const hU hf hn hx]
        rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hsymm.eq _ _
      -- all swaps
      have hswap : ∀ (a b : Fin (n + 2)) (m : Fin (n + 2) → E),
          iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap a b) =
            iteratedFDeriv ℝ (n + 2) f x m := by
        have h0b : ∀ (j : Fin (n + 1)) (m : Fin (n + 2) → E),
            iteratedFDeriv ℝ (n + 2) f x (m ∘ Equiv.swap 0 j.succ) =
              iteratedFDeriv ℝ (n + 2) f x m := by
          intro j m
          by_cases hj : j = 0
          · subst hj
            exact h01 m
          · -- conjugate the first swap by the tail swap `τ = (1 j.succ)`
            let τ : Equiv.Perm (Fin (n + 2)) := Equiv.swap (0 : Fin (n + 1)).succ j.succ
            have hτ0 : τ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm
              (Fin.succ_ne_zero _).symm
            have hτ1 : τ 1 = j.succ := Equiv.swap_apply_left _ _
            have hconj : Equiv.swap 0 j.succ = τ * Equiv.swap 0 1 * τ := by
              have := Equiv.swap_apply_apply τ 0 1
              rw [hτ0, hτ1] at this
              rw [this, Equiv.swap_inv]
            have e1 : iteratedFDeriv ℝ (n + 2) f x (m ∘ (τ * Equiv.swap 0 1 * τ : Equiv.Perm _)) =
                iteratedFDeriv ℝ (n + 2) f x (((m ∘ τ) ∘ Equiv.swap 0 1) ∘ τ) := rfl
            rw [hconj, e1, htail, h01, htail]
        intro a b m
        cases a using Fin.cases with
        | zero =>
          cases b using Fin.cases with
          | zero => simp
          | succ j => exact h0b j m
        | succ i =>
          cases b using Fin.cases with
          | zero => rw [Equiv.swap_comm]; exact h0b i m
          | succ j => exact htail i j m
      induction σ using Equiv.Perm.swap_induction_on generalizing m with
      | one => rfl
      | swap_mul g a b _ ihg =>
        have e1 : iteratedFDeriv ℝ (n + 2) f x (m ∘ (Equiv.swap a b * g : Equiv.Perm _)) =
            iteratedFDeriv ℝ (n + 2) f x ((m ∘ Equiv.swap a b) ∘ g) := rfl
        rw [e1, ihg, hswap]

end Submission.Obl.k4_approximate_conic_taylor_decomposition
