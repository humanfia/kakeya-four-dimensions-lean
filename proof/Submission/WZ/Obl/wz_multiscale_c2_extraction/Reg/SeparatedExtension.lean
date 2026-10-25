-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.SeparatedExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.AffineCutoff

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set

noncomputable section

/-- A sum of functions with disjoint prescribed supports has the same pointwise bound
as its individual terms. This avoids a loss equal to the number of intervals. -/
theorem abs_sum_le_of_disjoint {I : Type*} [Fintype I] {X : Type*}
    (S : I → Set X) (F : I → X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hsep : Pairwise fun i j => Disjoint (S i) (S j))
    (hzero : ∀ i x, x ∉ S i → F i x = 0) (hbound : ∀ i x, |F i x| ≤ B)
    (x : X) : |∑ i, F i x| ≤ B := by
  classical
  by_cases hx : ∃ i, x ∈ S i
  · obtain ⟨i, hi⟩ := hx
    have he : (∑ j, F j x) = F i x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply hzero
        exact fun hj => Set.disjoint_left.mp (hsep hji) hj hi
      · simp
    rw [he]
    exact hbound i x
  · have he : ∀ i, F i x = 0 := fun i => hzero i x (fun hi => hx ⟨i, hi⟩)
    simp only [he, Finset.sum_const_zero, abs_zero]
    exact hB

/-- Smooth interpolation on a finite collection of separated affine intervals.
The derivative bounds depend on the worst affine datum, not on the number of intervals. -/
theorem exists_smooth_separated_affine_extension : ∃ C : ℝ, 0 < C ∧
    ∀ (I : Type) [Fintype I] (l u a y s : I → ℝ) (B₁ B₂ : ℝ),
      (∀ i, 0 < a i) →
      (Pairwise fun i j => Disjoint (Icc (l i - a i) (u i + a i))
        (Icc (l j - a j) (u j + a j))) →
      0 ≤ B₁ → 0 ≤ B₂ →
      (∀ i, (|y i| + |y i + s i * (u i - l i)|) / a i + |s i| ≤ B₁) →
      (∀ i, (|y i| + |y i + s i * (u i - l i)|) / (a i) ^ 2 + |s i| / a i ≤ B₂) →
      ∃ G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧
        (∀ i x, x ∈ Icc (l i) (u i) → G x = y i + s i * (x - l i)) ∧
        (∀ x, (∀ i, x ∉ Icc (l i - a i) (u i + a i)) → G x = 0) ∧
        (∀ x, |deriv G x| ≤ C * B₁) ∧
        (∀ x, |deriv (deriv G) x| ≤ C * B₂) := by
  obtain ⟨K, hK, hbound⟩ := exists_transition_deriv_bound
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let C := 8 * (K + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro I _ l u a y s B₁ B₂ ha hsep hB₁ hB₂ hb₁ hb₂
  classical
  let F : I → ℝ → ℝ := fun i => affineExtension (l i) (u i) (a i) (y i) (s i)
  let S : I → Set ℝ := fun i => Icc (l i - a i) (u i + a i)
  let G : ℝ → ℝ := fun x => ∑ i, F i x
  have hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i) := fun i => affineExtension_contDiff ..
  have hFzero : ∀ i x, x ∉ S i → F i x = 0 := fun i x hx =>
    affineExtension_zero_of_not_mem (ha i) hx
  have hFderiv : ∀ i, Differentiable ℝ (F i) := fun i => (hF i).differentiable (by simp)
  have hF₂ : ∀ i, ContDiff ℝ 2 (F i) := fun i => (hF i).of_le (by simp)
  have hFderiv' : ∀ i, Differentiable ℝ (deriv (F i)) := fun i =>
    (hF₂ i).differentiable_deriv_two
  have hGderiv : deriv G = fun x => ∑ i, deriv (F i) x := by
    have he : (∑ i, F i) = G := by funext t; simp [G]
    rw [← he]
    funext x
    exact deriv_sum (u := Finset.univ) (fun i _ => hFderiv i x)
  have hGderiv' : deriv (deriv G) = fun x => ∑ i, deriv (deriv (F i)) x := by
    rw [hGderiv]
    have he : (∑ i, deriv (F i)) = (fun x => ∑ i, deriv (F i) x) := by funext t; simp
    rw [← he]
    funext x
    exact deriv_sum (u := Finset.univ) (fun i _ => hFderiv' i x)
  refine ⟨G, ContDiff.sum (fun i _ => hF i), ?_, ?_, ?_, ?_⟩
  · intro i x hx
    have hxi : x ∈ S i := ⟨by linarith [hx.1, ha i], by linarith [hx.2, ha i]⟩
    have he : G x = F i x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hFzero j x (fun hxj => Set.disjoint_left.mp (hsep hji) hxj hxi)
      · simp
    exact he.trans (affineExtension_eq_affine (ha i) hx)
  · intro x hx
    exact Finset.sum_eq_zero (fun i _ => hFzero i x (hx i))
  · intro x
    rw [hGderiv]
    apply abs_sum_le_of_disjoint S (fun i => deriv (F i)) (mul_nonneg hC.le hB₁) hsep
    · intro i x hx
      exact (affineExtension_derivs_zero_of_not_mem (ha i) hx).1
    · intro i x
      have hai : 0 < a i := ha i
      calc |deriv (F i) x| ≤ (2 * K + 1) *
          ((|y i| + |y i + s i * (u i - l i)|) / a i + |s i|) :=
            affineExtension_deriv_bound hK0 (fun x => (hbound x).1) (ha i) ..
        _ ≤ C * ((|y i| + |y i + s i * (u i - l i)|) / a i + |s i|) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [C]; nlinarith
          · positivity
        _ ≤ C * B₁ := mul_le_mul_of_nonneg_left (hb₁ i) hC.le
  · intro x
    rw [hGderiv']
    apply abs_sum_le_of_disjoint S (fun i => deriv (deriv (F i))) (mul_nonneg hC.le hB₂) hsep
    · intro i x hx
      exact (affineExtension_derivs_zero_of_not_mem (ha i) hx).2
    · intro i x
      have hai : 0 < a i := ha i
      calc |deriv (deriv (F i)) x| ≤ (6 * K + 2 * K ^ 2) *
          ((|y i| + |y i + s i * (u i - l i)|) / (a i) ^ 2 + |s i| / a i) :=
            affineExtension_deriv_deriv_bound hK0 hbound (ha i) ..
        _ ≤ C * ((|y i| + |y i + s i * (u i - l i)|) / (a i) ^ 2 + |s i| / a i) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [C]; nlinarith
          · positivity
        _ ≤ C * B₂ := mul_le_mul_of_nonneg_left (hb₂ i) hC.le

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
