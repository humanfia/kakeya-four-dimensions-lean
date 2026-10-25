-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.DifferenceExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.NestedExtension

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set

private theorem value_bound_of_support {g : ℝ → ℝ} {B : ℝ}
    (hg : Differentiable ℝ g) (hB : 0 ≤ B)
    (hderiv : ∀ z, |deriv g z| ≤ B)
    (hzero : ∀ z, z ∉ Icc (-2 : ℝ) 2 → g z = 0) :
    ∀ z, |g z| ≤ 5 * B := by
  intro z
  by_cases hz : z ∈ Icc (-2 : ℝ) 2
  · have h3 : g 3 = 0 := hzero 3 (by norm_num)
    have hb := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := (univ : Set ℝ)) (fun x _ => hg x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hderiv x)
      convex_univ (mem_univ (3 : ℝ)) (mem_univ z)
    have hdist : |z - 3| ≤ 5 := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    rw [h3, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hdist hB).trans_eq (mul_comm _ _))
  · rw [hzero z hz, abs_zero]
    positivity

/-- Smooth the successive differences of arbitrary affine fits. At each level,
compact samples provide both endpoints of the correction interval. The intervals
at different levels need not be nested: their values telescope pointwise.

The geometric selection is explicit in the hypotheses: sample hulls must be long
enough, separated after padding, and cover every retained height at every level. -/
theorem exists_smooth_difference_extension : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (I : Fin N → Type) [∀ k, Fintype (I k)]
      (A : Fin (N + 1) → ℝ → ℝ) (S : ∀ k, I k → Set ℝ)
      (b s : ∀ k, I k → ℝ) (a H : Fin N → ℝ)
      (D : Set ℝ) (f : ℝ → ℝ) (δ : ℝ),
      (∀ k, 0 < a k) → (∀ k, a k ≤ 1) → (∀ k, 0 ≤ H k) →
      (∀ k i, IsCompact (S k i)) → (∀ k i, (S k i).Nonempty) →
      (∀ k i, S k i ⊆ Icc (-1 : ℝ) 1) →
      (∀ k i, a k ≤ sSup (S k i) - sInf (S k i)) →
      (∀ k, Pairwise fun i j =>
        Disjoint (Icc (sInf (S k i) - a k) (sSup (S k i) + a k))
          (Icc (sInf (S k j) - a k) (sSup (S k j) + a k))) →
      (∀ k i z, z ∈ Icc (sInf (S k i)) (sSup (S k i)) →
        A k.succ z - A k.castSucc z = b k i + s k i * z) →
      (∀ k i z, z ∈ S k i → |A k.succ z - A k.castSucc z| ≤ H k) →
      (∀ z, A 0 z = 0) →
      (∀ z ∈ D, ∀ k, ∃ i, z ∈ Icc (sInf (S k i)) (sSup (S k i))) →
      (∀ z ∈ D, |f z - A (Fin.last N) z| ≤ δ) →
      ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ z ∈ D, |f z - g z| ≤ δ) ∧
        (∀ z, |g z| ≤ C * ∑ k, H k / a k) ∧
        (∀ z, |deriv g z| ≤ C * ∑ k, H k / a k) ∧
        (∀ z, |deriv (deriv g) z| ≤ C * ∑ k, H k / (a k) ^ 2) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_multiscale_extension_supported
  refine ⟨20 * C, by positivity, ?_⟩
  intro N I _ A S b s a H D f δ ha ha1 hH hS hSne hSbox hlen hsep
    haffine herror hzero hcover happrox
  classical
  let l : ∀ k, I k → ℝ := fun k i => sInf (S k i)
  let u : ∀ k, I k → ℝ := fun k i => sSup (S k i)
  let y : ∀ k, I k → ℝ := fun k i => b k i + s k i * l k i
  have hll : ∀ k i, l k i ≤ u k i := fun k i => by
    have hh := hlen k i
    have hh' := (ha k).le
    dsimp [l, u]
    linarith
  have hlmem : ∀ k i, l k i ∈ S k i := fun k i => (hS k i).sInf_mem (hSne k i)
  have humem : ∀ k i, u k i ∈ S k i := fun k i => (hS k i).sSup_mem (hSne k i)
  have hcorrection : ∀ k i z, y k i + s k i * (z - l k i) = b k i + s k i * z := by
    intro k i z
    dsimp [y]
    ring
  have hbudgets : ∀ k i,
      (|y k i| + |y k i + s k i * (u k i - l k i)|) / a k + |s k i| ≤
        4 * (H k / a k) ∧
      (|y k i| + |y k i + s k i * (u k i - l k i)|) / (a k) ^ 2 + |s k i| / a k ≤
        4 * (H k / (a k) ^ 2) := by
    intro k i
    apply affine_correction_budgets (ha k) (hlen k i) (hH k)
    · dsimp [y]
      rw [← haffine k i (l k i) ⟨le_rfl, hll k i⟩]
      exact herror k i _ (hlmem k i)
    · rw [hcorrection, ← haffine k i (u k i) ⟨hll k i, le_rfl⟩]
      exact herror k i _ (humem k i)
  have hsum : ∀ z ∈ D, ∃ path : ∀ k, I k,
      (∀ k, z ∈ Icc (l k (path k)) (u k (path k))) ∧
      |f z - ∑ k, (y k (path k) + s k (path k) * (z - l k (path k)))| ≤ δ := by
    intro z hz
    choose path hpath using hcover z hz
    refine ⟨path, hpath, ?_⟩
    have heq : (∑ k, (y k (path k) + s k (path k) * (z - l k (path k)))) =
        A (Fin.last N) z := by
      simp_rw [hcorrection, ← haffine _ _ _ (hpath _)]
      rw [sum_affine_differences (fun k => A k z), hzero, sub_zero]
    rw [heq]
    exact happrox z hz
  obtain ⟨g, hg, hgf, hgsupport, hg₁, hg₂⟩ :=
    hext (Fin N) I l u (fun k _ => a k) y s
      (fun k => 4 * (H k / a k)) (fun k => 4 * (H k / (a k) ^ 2))
      D f δ (fun k _ => ha k) hsep
      (fun k => mul_nonneg (by norm_num) (div_nonneg (hH k) (ha k).le))
      (fun k => mul_nonneg (by norm_num) (div_nonneg (hH k) (sq_nonneg _)))
      (fun k i => (hbudgets k i).1) (fun k i => (hbudgets k i).2) hsum
  have hsupport : ∀ z, z ∉ Icc (-2 : ℝ) 2 → g z = 0 := by
    intro z hz
    apply hgsupport z
    intro k i hzi
    apply hz
    have hl := (hSbox k i (hlmem k i)).1
    have hu := (hSbox k i (humem k i)).2
    constructor <;> linarith [hzi.1, hzi.2, ha1 k]
  have hb₁ : ∀ z, |deriv g z| ≤ (4 * C) * ∑ k, H k / a k := by
    intro z
    simpa only [← Finset.mul_sum, mul_assoc, mul_comm C] using hg₁ z
  have hb₂ : ∀ z, |deriv (deriv g) z| ≤ (4 * C) * ∑ k, H k / (a k) ^ 2 := by
    intro z
    simpa only [← Finset.mul_sum, mul_assoc, mul_comm C] using hg₂ z
  refine ⟨g, hg, hgf, ?_, ?_, ?_⟩
  · intro z
    have hh := value_bound_of_support (hg.differentiable (by simp))
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun k _ => div_nonneg (hH k) (ha k).le))) hb₁ hsupport z
    convert hh using 1 <;> ring
  · intro z
    exact (hb₁ z).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Finset.sum_nonneg (fun k _ => div_nonneg (hH k) (ha k).le)))
  · intro z
    exact (hb₂ z).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Finset.sum_nonneg (fun k _ => div_nonneg (hH k) (sq_nonneg _))))

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
