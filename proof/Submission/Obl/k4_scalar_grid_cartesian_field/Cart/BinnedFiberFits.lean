-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/BinnedFiberFits.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set

theorem polynomial_eval_difference_of_coefficients (D : ℕ) (p q : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D)
    (E B : ℝ) (hE : 0 ≤ E) (hB : 1 ≤ B)
    (hcoeff : ∀ k ≤ D, |p.coeff k-q.coeff k| ≤ E)
    (t : ℝ) (ht : |t| ≤ B) :
    |p.eval t-q.eval t| ≤ ((D : ℝ)+1)*E*B^D := by
  classical
  have hdeg : (p-q).natDegree < D+1 :=
    Nat.lt_succ_of_le ((Polynomial.natDegree_sub_le _ _).trans (max_le hp hq))
  rw [← Polynomial.eval_sub, Polynomial.eval_eq_sum_range' hdeg t]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (D+1), E*B^D := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [abs_mul, Polynomial.coeff_sub, abs_pow]
      have hpow : |t|^k ≤ B^D :=
        (pow_le_pow_left₀ (abs_nonneg t) ht k).trans (pow_le_pow_right₀ hB hkD)
      exact mul_le_mul (hcoeff k hkD) hpow (pow_nonneg (abs_nonneg _) _) hE
    _ = _ := by simp [nsmul_eq_mul]; ring

theorem polynomial_eval_difference_of_common_bins (D : ℕ) (p q : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D)
    (ε B : ℝ) (hε : 0 < ε) (hB : 1 ≤ B)
    (hbin : ∀ k : Fin (D+1), ⌊p.coeff k / ε⌋ = ⌊q.coeff k / ε⌋)
    (t : ℝ) (ht : |t| ≤ B) :
    |p.eval t-q.eval t| ≤ 2*((D : ℝ)+1)*ε*B^D := by
  have hcoeff (k : ℕ) (hk : k ≤ D) : |p.coeff k-q.coeff k| ≤ 2*ε := by
    have hkp := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hε (p.coeff k)
    have hkq := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hε (q.coeff k)
    have heq := hbin ⟨k, Nat.lt_succ_of_le hk⟩
    rw [heq] at hkp
    have htri := (abs_sub_le (p.coeff k) (ε*(⌊q.coeff k/ε⌋ : ℝ)) (q.coeff k)).trans
      (add_le_add hkp (by simpa only [abs_sub_comm] using hkq))
    linarith
  have h := polynomial_eval_difference_of_coefficients D p q hp hq (2*ε) B
    (by positivity) hB hcoeff t ht
  convert h using 1 <;> ring

/-- Fixing coefficient bins along a fiber makes one actual witness
polynomial fit every occupied point of that fiber. -/
theorem exists_fiber_polynomial_of_common_bins {Ω X Y : Type*}
    (A : Set Ω) (cell : Ω → X × Y) (v : X → ℝ) (f : X → Y → ℝ)
    (G : Ω → ℝ) (P : Ω → Polynomial ℝ) (D : ℕ) (ε B E₀ E₁ : ℝ)
    (hε : 0 < ε) (hB : 1 ≤ B) (hv : ∀ x, |v x| ≤ B)
    (hdegree : ∀ ω ∈ A, (P ω).natDegree ≤ D)
    (hfield : ∀ ω ∈ A, |f (cell ω).1 (cell ω).2 - G ω| ≤ E₀)
    (hfit : ∀ ω ∈ A, |G ω - (P ω).eval (v (cell ω).1)| ≤ E₁)
    (hbins : ∀ ω ∈ A, ∀ ω' ∈ A, (cell ω).2 = (cell ω').2 →
      ∀ k : Fin (D+1), ⌊(P ω).coeff k/ε⌋ = ⌊(P ω').coeff k/ε⌋) :
    ∀ y, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ x, (∃ ω ∈ A, cell ω = (x,y)) →
        |f x y - p.eval (v x)| ≤ E₀+E₁+2*((D : ℝ)+1)*ε*B^D := by
  classical
  intro y
  by_cases hex : ∃ ω ∈ A, (cell ω).2 = y
  · obtain ⟨ω₀,hω₀,hy₀⟩ := hex
    refine ⟨P ω₀,hdegree ω₀ hω₀,?_⟩
    intro x hx
    obtain ⟨ω,hω,hcell⟩ := hx
    have hsame : (cell ω).2 = (cell ω₀).2 := by simpa only [hcell] using hy₀.symm
    have hpoly := polynomial_eval_difference_of_common_bins D (P ω) (P ω₀)
      (hdegree ω hω) (hdegree ω₀ hω₀) ε B hε hB (hbins ω hω ω₀ hω₀ hsame) (v x) (hv x)
    have hf := hfield ω hω
    have hp := hfit ω hω
    rw [hcell] at hf hp
    exact (abs_sub_le (f x y) (G ω) ((P ω₀).eval (v x))).trans
      (add_le_add hf ((abs_sub_le (G ω) ((P ω).eval (v x)) ((P ω₀).eval (v x))).trans
        (add_le_add hp hpoly))) |>.trans_eq (by ring)
  · refine ⟨0, by simp, ?_⟩
    intro x hx
    obtain ⟨ω,hω,hcell⟩ := hx
    exact (hex ⟨ω,hω,by rw [hcell]⟩).elim

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
