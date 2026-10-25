-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GeometricSmoothing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridPower

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

/-- Geometric grids give a uniform power budget, independent of the number of
cells or of how the grids align. The two terms in the mass loss come from thin
sample hulls and cells crossing the preceding grid, respectively. -/
theorem exists_smooth_geometric_approximation : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (t ζ : ℝ) (μ : Measure ℝ) (L : ℝ) (D : Set ℝ) (f : ℝ → ℝ)
      (A : Fin (N + 1) → ℝ → ℝ),
      0 < N → 0 < t → t ≤ 1 → 0 ≤ ζ → 0 ≤ L →
      (∀ l u : ℝ, μ (Icc l u) ≤ ENNReal.ofReal L * ENNReal.ofReal (u - l)) →
      IsCompact D → D ⊆ Icc (-1 : ℝ) 1 →
      (∀ k, AffineOnGrid (geometricWidth t N k) (A k)) → (∀ z, A 0 z = 0) →
      (∀ k z, z ∈ D → |f z - A k z| ≤ geometricError t N k) →
      (∀ z ∈ D, |f z - A (Fin.last N) z| ≤ t) →
      ∃ (D' : Set ℝ) (g : ℝ → ℝ), D' ⊆ D ∧ IsCompact D' ∧
        μ D ≤ μ D' + ENNReal.ofReal (55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) ∧
        ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ z ∈ D', |f z - g z| ≤ t) ∧
        ∀ z, |g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv (deriv g) z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_grid_approximation
  refine ⟨6 * C, by positivity, ?_⟩
  intro N t ζ μ L D f A hN ht ht1 hζ hL hμ hD hDbox hgrid hzero hfit hfinal
  obtain ⟨D', g, hD'sub, hD'c, hmass, hg, hgf, hg₀, hg₁, hg₂⟩ :=
    hext N μ L D f A (geometricWidth t N) (geometricError t N) (geometricPadding t ζ N) t
      hL hμ hD hDbox (geometricWidth_pos ht N) (geometricWidth_le_one ht ht1 N)
      (fun k => by unfold geometricError; positivity)
      (geometricPadding_pos ht N) (geometricPadding_le_one ht ht1 hζ N)
      hgrid hzero hfit hfinal
  have hb₁ : C * (∑ k : Fin N,
      (geometricError t N k.succ + geometricError t N k.castSucc) / geometricPadding t ζ N k) ≤
      (6 * C) * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
    calc
      _ ≤ C * ∑ _k : Fin N, 6 * t ^ (-(1 / (N : ℝ) + 2 * ζ)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun k _ => geometric_first_budget ht ht1 hζ hN k)) hC.le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hb₂ : C * (∑ k : Fin N,
      (geometricError t N k.succ + geometricError t N k.castSucc) / (geometricPadding t ζ N k) ^ 2) ≤
      (6 * C) * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
    calc
      _ ≤ C * ∑ _k : Fin N, 6 * t ^ (-(1 / (N : ℝ) + 2 * ζ)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun k _ => geometric_second_budget ht ht1 hN k)) hC.le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine ⟨D', g, hD'sub, hD'c, ?_, hg, hgf,
    fun z => ⟨(hg₀ z).trans hb₁, (hg₁ z).trans hb₁, (hg₂ z).trans hb₂⟩⟩
  simp_rw [geometricPadding_ratio ht, geometricWidth_ratio ht hN] at hmass
  have he : (∑ _k : Fin N, ENNReal.ofReal (55 * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ)))))) =
      ENNReal.ofReal (55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show 55 * (N : ℝ) * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ)))) =
      (N : ℝ) * (55 * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) by ring]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rwa [he] at hmass

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
