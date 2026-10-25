import Submission.Obl.k4_general_wide_layer_offset_comparison.Layers

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- The moving interval bound calibrates every coefficient, independently of the
intercept mesh. The fixed separation between `m` and `r` absorbs this cost. -/
theorem eventually_layer_coefficients {α : Type} [MeasurableSpace α]
    (p : Parameters) (M : PreparedModel α) (hp : p.Valid)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) {H : ℕ → ℝ}
    (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε)
    {r u v m : ℝ} (hexp : ComparisonExponents p.d p.kappa p.ell p.U r u v m)
    (L : ℕ → Fin 3 → ProjLayer α)
    (hL : ∀ k a, LayerValid p M (τ k) (depth r u v a) m (H k) (L k a)) :
    ∀ᶠ k in atTop, ∀ a i e, |((L k a).G i).coeff e| ≤ p.N (τ k) ^ (m / 1000) := by
  obtain ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he⟩ := hp
  obtain ⟨C, hC, hcoeff⟩ :=
    Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.exists_strip_coeff_bound
  have hr : 0 < r := hexp.1.1
  have hgap : 4 * p.ell * r < m / 1000 := by
    have := hexp.2.2.2.2.1
    nlinarith
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (N := fun k => p.N (τ k)) (K := H) (fun k => by linarith [hN (τ k)])
    (hNt.comp hτ.tendsto_atTop) hH hHsub 5 hgap hC.le
  filter_upwards [hsmall, hHsub (p.ell * r / 2) (by positivity)] with k hk hHk
  have hNp : 0 < p.N (τ k) := by linarith [hN (τ k)]
  have hN1 : 1 ≤ p.N (τ k) := by linarith [hN (τ k)]
  have hHp : 0 < H k := zero_lt_one.trans_le (hH k)
  intro a i e
  have hs : r ≤ depth r u v a ∧ depth r u v a ≤ 2 * r := by
    fin_cases a <;> constructor <;> dsimp [depth] <;> linarith [hexp.1.2.1,
      hexp.1.2.2.1, hexp.2.1, hexp.2.2.1]
  obtain ⟨hβ, hβlo, hβhi, hmeas, hdisj, hi⟩ := (hL k a).1
  simp only [neg_zero, Real.rpow_zero, mul_one] at hβlo
  obtain ⟨huv, hdeg, hnorm, hfit, hfloor⟩ := hi i
  have hβ1 : (L k a).β ≤ 1 := by
    calc
      _ ≤ H k * p.N (τ k) ^ (-p.ell * depth r u v a) := hβhi
      _ ≤ p.N (τ k) ^ (p.ell * r / 2) * p.N (τ k) ^ (-p.ell * r) := by
        exact mul_le_mul hHk
          (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith [hs.1]))
          (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
      _ = p.N (τ k) ^ (p.ell * r / 2 + -p.ell * r) := (Real.rpow_add hNp _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  have hβinv : (L k a).β⁻¹ ≤ H k * p.N (τ k) ^ (p.ell * depth r u v a) := by
    have hh := inv_anti₀ (div_pos (Real.rpow_pos_of_pos hNp _) hHp) hβlo
    calc
      _ ≤ (p.N (τ k) ^ (-p.ell * depth r u v a) / H k)⁻¹ := hh
      _ = H k * p.N (τ k) ^ (p.ell * depth r u v a) := by
        rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg hNp.le]
        congr 2
        ring
  have hb := hcoeff ((L k a).G i) hdeg ((L k a).u i) ((L k a).v i)
    (L k a).β (H k) (H k) hβ hβ1 (hH k)
    (by linarith [abs_nonneg ((L k a).v i)])
    (by linarith [abs_nonneg ((L k a).u i)]) hHp.le hnorm e
  calc
    _ ≤ C * H k * H k ^ 2 / (L k a).β ^ 2 := hb
    _ = C * H k * H k ^ 2 * ((L k a).β⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ C * H k * H k ^ 2 *
        (H k * p.N (τ k) ^ (p.ell * depth r u v a)) ^ 2 := by
      gcongr
    _ = C * H k ^ 5 * p.N (τ k) ^ (2 * p.ell * depth r u v a) := by
      have hpow : (p.N (τ k) ^ (p.ell * depth r u v a)) ^ (2 : ℕ) =
          p.N (τ k) ^ (2 * p.ell * depth r u v a) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
        congr 1
        ring
      rw [mul_pow, hpow]
      ring
    _ ≤ C * H k ^ 5 * p.N (τ k) ^ (4 * p.ell * r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith [hs.2])
    _ ≤ p.N (τ k) ^ (m / 1000) := hk.le

end

end Submission.Obl.k4_general_wide_layer_offset_comparison
