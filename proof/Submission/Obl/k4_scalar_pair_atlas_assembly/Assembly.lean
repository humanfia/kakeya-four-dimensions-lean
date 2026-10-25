import Submission.Obl.k4_scalar_pair_atlas_assembly.Tables

-- Adapted from this LOT obligation, x0578/440ea3f, Assembly.lean.

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

theorem coarse_time_bound (N₀ : ℕ → ℝ) (hN : ∀ k, 2 ≤ N₀ k)
    (hlim : Tendsto N₀ atTop atTop) (h e ε σ : ℝ)
    (heh : e < h) (hσ : 0 < σ) (hσε : σ ≤ ε / 2) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ T T₁ : ℕ,
      (2 : ℝ) ^ T ≤ N₀ k ^ (h + σ) →
      (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * N₀ k ^ (-e)) →
      (2 : ℝ) ^ T₁ ≤ N₀ k ^ (h - e + ε) := by
  have hexp : 0 < ε - σ := by linarith
  have hgrowth := (tendsto_rpow_atTop hexp).comp hlim
  filter_upwards [hgrowth.eventually (eventually_ge_atTop (2 : ℝ))] with k hk
  intro T T₁ hT hT₁
  have hpos : 0 < N₀ k := lt_of_lt_of_le (by norm_num) (hN k)
  have hone : 1 ≤ N₀ k := by linarith [hN k]
  have hunit : 1 ≤ N₀ k ^ (h + σ - e) :=
    Real.one_le_rpow hone (by linarith)
  calc
    (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * N₀ k ^ (-e)) := hT₁
    _ ≤ 2 * max 1 (N₀ k ^ (h + σ) * N₀ k ^ (-e)) := by
      gcongr
    _ = 2 * N₀ k ^ (h + σ - e) := by
      rw [← Real.rpow_add hpos]
      change 2 * max 1 (N₀ k ^ (h + σ - e)) = _
      rw [max_eq_right hunit]
    _ ≤ N₀ k ^ (ε - σ) * N₀ k ^ (h + σ - e) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hpos.le _)
    _ = N₀ k ^ (h - e + ε) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring

theorem assemble (geometry : SparseTables) (installation : InstallTables) :
    ∀ p : Code, Exact p → ∀ h e a : ℝ,
      0 < e → e < h → 1 ≤ a → 0 < L p - (a + 10) * e →
      Prepared p h e a → Known p (L p - (a + 10) * e) (L p) (h - e) := by
  intro p hp h e a he heh ha hr hprep
  obtain ⟨B, hB, hprep⟩ := hprep
  obtain ⟨G, hG, hgeo⟩ := geometry p hp h e a he heh ha hr B hB
  obtain ⟨B', hB', hinst⟩ := installation p hp B G hB hG
  refine ⟨sub_nonneg.mpr heh.le, B', hB', ?_⟩
  intro ε hε
  obtain ⟨σ, hσ, hσε, hgeok⟩ := hgeo ε hε
  have htime := coarse_time_bound (N p) hp.1.1 hp.1.2.1 h e ε σ heh hσ hσε hε
  apply ((hprep σ hσ).and_eventually (hgeok.and htime)).mono
  rintro k ⟨⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc, T₁, hle, hratio, hcoarse, hmass⟩,
    hgeok, htime⟩
  obtain ⟨m, g, b, code, u', v', J', P', R, htable⟩ :=
    hgeok T n γ j A C u v J P Λ hc T₁ hle hratio hcoarse
  exact hinst (h + σ) (h - e + ε) (L p - (a + 10) * e) ε σ a e hε hσ hσε
    k T T₁ n γ j A C u v J P Λ hc hle (htime T T₁ hc.1 hcoarse)
    m g b code u' v' J' P' R htable hmass

end Submission.Obl.k4_scalar_pair_atlas_assembly
