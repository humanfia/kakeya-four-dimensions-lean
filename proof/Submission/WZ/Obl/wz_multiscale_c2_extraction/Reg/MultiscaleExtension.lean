-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.MultiscaleExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.SeparatedExtension

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set

noncomputable section

/-- Analytic gluing of affine corrections at finitely many scales. In an application,
the affine corrections are the differences between a trapezoid axis and its parent's
axis. Their sum along a nested chain telescopes to the finest-scale axis.

The hypotheses explicitly retain the missing geometric input: a large set of heights
with compatible affine approximations at every scale. This theorem does not assert
that such heights can be extracted from an extremal tube family. -/
theorem exists_smooth_multiscale_extension_supported : ∃ C : ℝ, 0 < C ∧
    ∀ (L : Type) [Fintype L] (I : L → Type) [∀ k, Fintype (I k)]
      (l u a y s : ∀ k, I k → ℝ) (B₁ B₂ : L → ℝ) (D : Set ℝ) (f : ℝ → ℝ) (δ : ℝ),
      (∀ k i, 0 < a k i) →
      (∀ k, Pairwise fun i j => Disjoint (Icc (l k i - a k i) (u k i + a k i))
        (Icc (l k j - a k j) (u k j + a k j))) →
      (∀ k, 0 ≤ B₁ k) → (∀ k, 0 ≤ B₂ k) →
      (∀ k i, (|y k i| + |y k i + s k i * (u k i - l k i)|) / a k i + |s k i| ≤ B₁ k) →
      (∀ k i, (|y k i| + |y k i + s k i * (u k i - l k i)|) / (a k i) ^ 2 +
        |s k i| / a k i ≤ B₂ k) →
      (∀ z ∈ D, ∃ b : ∀ k, I k,
        (∀ k, z ∈ Icc (l k (b k)) (u k (b k))) ∧
        |f z - ∑ k, (y k (b k) + s k (b k) * (z - l k (b k)))| ≤ δ) →
      ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ z ∈ D, |f z - g z| ≤ δ) ∧
        (∀ z, (∀ k i, z ∉ Icc (l k i - a k i) (u k i + a k i)) → g z = 0) ∧
        (∀ z, |deriv g z| ≤ C * ∑ k, B₁ k) ∧
        (∀ z, |deriv (deriv g) z| ≤ C * ∑ k, B₂ k) := by
  obtain ⟨C, hC, hCext⟩ := exists_smooth_separated_affine_extension
  refine ⟨C, hC, ?_⟩
  intro L _ I _ l u a y s B₁ B₂ D f δ ha hsep hB₁ hB₂ hb₁ hb₂ happrox
  have hlevel : ∀ k, ∃ G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∀ i x, x ∈ Icc (l k i) (u k i) → G x = y k i + s k i * (x - l k i)) ∧
      (∀ x, (∀ i, x ∉ Icc (l k i - a k i) (u k i + a k i)) → G x = 0) ∧
      (∀ x, |deriv G x| ≤ C * B₁ k) ∧
      (∀ x, |deriv (deriv G) x| ≤ C * B₂ k) := fun k =>
    hCext (I k) (l k) (u k) (a k) (y k) (s k) (B₁ k) (B₂ k)
      (ha k) (hsep k) (hB₁ k) (hB₂ k) (hb₁ k) (hb₂ k)
  choose G hGsmooth hGaffine hGzero hGbound₁ hGbound₂ using hlevel
  let g : ℝ → ℝ := fun x => ∑ k, G k x
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := ContDiff.sum (fun k _ => hGsmooth k)
  have hd : ∀ k, Differentiable ℝ (G k) := fun k => (hGsmooth k).differentiable (by simp)
  have hd₂ : ∀ k, Differentiable ℝ (deriv (G k)) := by
    intro k
    have hc : ContDiff ℝ 2 (G k) := (hGsmooth k).of_le (by simp)
    exact hc.differentiable_deriv_two
  have hderiv : deriv g = fun x => ∑ k, deriv (G k) x := by
    have he : (∑ k, G k) = g := by funext x; simp [g]
    rw [← he]
    funext x
    exact deriv_sum (u := Finset.univ) (fun k _ => hd k x)
  have hderiv₂ : deriv (deriv g) = fun x => ∑ k, deriv (deriv (G k)) x := by
    rw [hderiv]
    have he : (∑ k, deriv (G k)) = (fun x => ∑ k, deriv (G k) x) := by funext x; simp
    rw [← he]
    funext x
    exact deriv_sum (u := Finset.univ) (fun k _ => hd₂ k x)
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hb, he⟩ := happrox z hz
    have heq : g z = ∑ k, (y k (b k) + s k (b k) * (z - l k (b k))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hGaffine k (b k) z (hb k)
    rwa [heq]
  · intro z hz
    exact Finset.sum_eq_zero (fun k _ => hGzero k z (hz k))
  · intro z
    rw [hderiv]
    calc |∑ k, deriv (G k) z| ≤ ∑ k, |deriv (G k) z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, C * B₁ k := Finset.sum_le_sum (fun k _ => hGbound₁ k z)
      _ = C * ∑ k, B₁ k := (Finset.mul_sum ..).symm
  · intro z
    rw [hderiv₂]
    calc |∑ k, deriv (deriv (G k)) z| ≤ ∑ k, |deriv (deriv (G k)) z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, C * B₂ k := Finset.sum_le_sum (fun k _ => hGbound₂ k z)
      _ = C * ∑ k, B₂ k := (Finset.mul_sum ..).symm

/-- The original multiscale interface, forgetting the support information. -/
theorem exists_smooth_multiscale_extension : ∃ C : ℝ, 0 < C ∧
    ∀ (L : Type) [Fintype L] (I : L → Type) [∀ k, Fintype (I k)]
      (l u a y s : ∀ k, I k → ℝ) (B₁ B₂ : L → ℝ) (D : Set ℝ) (f : ℝ → ℝ) (δ : ℝ),
      (∀ k i, 0 < a k i) →
      (∀ k, Pairwise fun i j => Disjoint (Icc (l k i - a k i) (u k i + a k i))
        (Icc (l k j - a k j) (u k j + a k j))) →
      (∀ k, 0 ≤ B₁ k) → (∀ k, 0 ≤ B₂ k) →
      (∀ k i, (|y k i| + |y k i + s k i * (u k i - l k i)|) / a k i + |s k i| ≤ B₁ k) →
      (∀ k i, (|y k i| + |y k i + s k i * (u k i - l k i)|) / (a k i) ^ 2 +
        |s k i| / a k i ≤ B₂ k) →
      (∀ z ∈ D, ∃ b : ∀ k, I k,
        (∀ k, z ∈ Icc (l k (b k)) (u k (b k))) ∧
        |f z - ∑ k, (y k (b k) + s k (b k) * (z - l k (b k)))| ≤ δ) →
      ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ z ∈ D, |f z - g z| ≤ δ) ∧
        (∀ z, |deriv g z| ≤ C * ∑ k, B₁ k) ∧
        (∀ z, |deriv (deriv g) z| ≤ C * ∑ k, B₂ k) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_multiscale_extension_supported
  refine ⟨C, hC, ?_⟩
  intro L _ I _ l u a y s B₁ B₂ D f δ ha hsep hB₁ hB₂ hb₁ hb₂ happrox
  obtain ⟨g, hg, hgf, _, hg₁, hg₂⟩ :=
    hext L I l u a y s B₁ B₂ D f δ ha hsep hB₁ hB₂ hb₁ hb₂ happrox
  exact ⟨g, hg, hgf, hg₁, hg₂⟩

/-- The affine correction between nested axes has slope controlled by its endpoint error. -/
theorem affine_slope_bound_of_endpoints {l u y s H : ℝ} (hlu : l < u)
    (hl : |y| ≤ H) (hu : |y + s * (u - l)| ≤ H) : |s| ≤ 2 * H / (u - l) := by
  apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
  calc |s| * (u - l) = |(y + s * (u - l)) - y| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos (sub_pos.mpr hlu)]
    _ ≤ |y + s * (u - l)| + |y| := abs_sub _ _
    _ ≤ 2 * H := by linarith

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
