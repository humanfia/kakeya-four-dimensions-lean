import Mathlib

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

/-- A factorial-free Taylor estimate, obtained by successively integrating a derivative chain. -/
lemma derivativeChain_bound (n : ℕ) (G : ℕ → ℝ → ℝ) {δ A t s : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hst : |s - t| ≤ δ)
    (hG : ∀ k, k < n → ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (G k) (G (k + 1) x) x)
    (hinit : ∀ k, k ≤ n → |G k t| * δ ^ k ≤ A)
    (htop : ∀ x ∈ Icc (0 : ℝ) 1, |G n x| * δ ^ n ≤ A) :
    |G 0 s| ≤ (n + 1 : ℕ) * A := by
  induction n generalizing G A s with
  | zero => simpa using htop s hs
  | succ n ih =>
    have hA' : 0 ≤ A / δ := div_nonneg hA hδ.le
    have hinit' (k : ℕ) (hk : k ≤ n) : |G (k + 1) t| * δ ^ k ≤ A / δ := by
      apply (le_div_iff₀ hδ).2
      simpa [pow_succ, mul_assoc] using hinit (k + 1) (by omega)
    have htop' (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
        |G (n + 1) x| * δ ^ n ≤ A / δ := by
      apply (le_div_iff₀ hδ).2
      simpa [pow_succ, mul_assoc] using htop x hx
    have hbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hxt : |x - t| ≤ δ) :
        |G 1 x| ≤ (n + 1 : ℕ) * (A / δ) := by
      exact ih (fun k => G (k + 1)) hA' hx hxt
        (fun k hk y hy => by simpa [Nat.add_assoc] using hG (k + 1) (by omega) y hy)
        hinit' htop'
    let T : Set ℝ := Icc 0 1 ∩ Icc (t - δ) (t + δ)
    have htT : t ∈ T := ⟨ht, by constructor <;> linarith⟩
    have hsT : s ∈ T := ⟨hs, by rcases abs_le.mp hst with ⟨h1, h2⟩; constructor <;> linarith⟩
    have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := G 0) (f' := G 1) (C := (n + 1 : ℕ) * (A / δ))
      (fun x hx => (hG 0 (by omega) x hx.1).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        apply hbound x hx.1
        apply abs_le.mpr
        constructor <;> linarith [hx.2.1, hx.2.2])
      ((convex_Icc (0 : ℝ) 1).inter (convex_Icc (t - δ) (t + δ))) htT hsT
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hd
    have hC : 0 ≤ (n + 1 : ℕ) * (A / δ) := by positivity
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hst hC)
    have hzero : |G 0 t| ≤ A := by simpa using hinit 0 (by omega)
    have htri : |G 0 s| ≤ |G 0 s - G 0 t| + |G 0 t| := by
      simpa using abs_add_le (G 0 s - G 0 t) (G 0 t)
    have he : ((n + 1 : ℕ) : ℝ) * (A / δ) * δ = ((n + 1 : ℕ) : ℝ) * A := by
      field_simp
    rw [he] at hd'
    push_cast at hd' ⊢
    linarith

lemma contDiffOn_iteratedDeriv {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (m k : ℕ) (hf : ContDiffOn ℝ (m + k : ℕ) f U) :
    ContDiffOn ℝ m (iteratedDeriv k f) U := by
  induction k generalizing f with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ']
    apply ih
    exact hf.deriv_of_isOpen hU (by norm_cast)

lemma hasDerivAt_iteratedDeriv {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} {M k : ℕ} (hf : ContDiffOn ℝ M f U)
    (hk : k < M) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hc : ContDiffOn ℝ 1 (iteratedDeriv k f) U :=
    contDiffOn_iteratedDeriv hU 1 k (hf.of_le (by norm_cast; omega))
  rw [iteratedDeriv_succ]
  exact ((hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

end Submission.Obl.k4_matching_homogeneous_records
