import Submission.Obl.k4_angular_normal_pair_preparation.Pruning

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Filter
open scoped ENNReal BigOperators

/-- A uniform eventual estimate on deleted rows lifts to the frozen cofinal package.
The original format bounds and the fixed grid of depths are retained. -/
theorem nativeSequence_prune
    {N : ℕ → ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S A R e h : ℝ}
    (hN : ∀ k, 1 ≤ N k) (hB : ∀ k γ₀, 0 ≤ B k γ₀) (he : 0 < e) (hAR : A ≤ R)
    (hnative : NativeSequence False 8 N W ω ν E P B f g G L S (A * e) e (R * e) h)
    (hbad : ∀ (M D : ℕ) (depths : Finset ℝ) (ε : ℝ), 0 < ε → ε ≤ e →
      ∀ᶠ k in atTop, ∀ q : NativeSample False 8 (N k) (W k) (ω k) (ν k) (E k)
        (P k) (B k) f (g k) (G k) L S (A * e) e (R * e) h M D depths ε,
        q.badMass (R * e) ≤ ENNReal.ofReal (4 * q.κ⁻¹)) :
    NativeSequence True 4 N W ω ν E P B f g G L S (R * e) e (R * e) h := by
  classical
  obtain ⟨M, D, depths, hzero, hL, hdepths, hgrid, hfreq⟩ := hnative
  refine ⟨M, D, depths, hzero, hL, hdepths, hgrid, ?_⟩
  intro ε hε
  let ε₀ := min ε e
  have hε₀ : 0 < ε₀ := lt_min hε he
  have hε₀e : ε₀ ≤ e := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  apply ((hfreq ε₀ hε₀).and_eventually (hbad M D depths ε₀ hε₀ hε₀e)).mono
  rintro k ⟨hk, hbk⟩
  obtain ⟨q⟩ := (nativeSample_nonempty_iff False 8 (N k) (W k) (ω k) (ν k) (E k)
    (P k) (B k) f (g k) (G k) L S (A * e) e (R * e) h M D depths ε₀).mpr hk
  let q' := q.prune (R * e) (hN k) (mul_le_mul_of_nonneg_right hAR he.le) (hB k) (hbk q)
  exact (nativeSample_nonempty_iff True 4 (N k) (W k) (ω k) (ν k) (E k)
    (P k) (B k) f (g k) (G k) L S (R * e) e (R * e) h M D depths ε).mp
      ⟨q'.withSlack ε (hN k) hε₀ε⟩

end Submission.Obl.k4_angular_normal_pair_preparation
