-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.FitSmoothing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GeometricSmoothing

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

/-- The finite affine fits from local linearity can be smoothed on most of a
height distribution with a bounded density. This is the analytic extraction
step after the tube geometry has produced those fits and that density bound. -/
theorem exists_smooth_from_affine_fits : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (t ζ : ℝ) (μ : Measure ℝ) (L : ℝ) (D : Set ℝ) (f : ℝ → ℝ)
      (B : Fin N → ℝ → ℝ),
      0 < N → 0 < t → t ≤ 1 → 0 ≤ ζ → 0 ≤ L →
      (∀ l u : ℝ, μ (Icc l u) ≤ ENNReal.ofReal L * ENNReal.ofReal (u - l)) →
      IsCompact D → D ⊆ Icc (-1 : ℝ) 1 → (∀ z ∈ D, |f z| ≤ 3) →
      (∀ k : Fin N, AffineOnGrid (Real.sqrt (t ^ (((k : ℝ) + 1) / N))) (B k)) →
      (∀ (k : Fin N) z, z ∈ D → |f z - B k z| ≤ t ^ (((k : ℝ) + 1) / N)) →
      ∃ (D' : Set ℝ) (g : ℝ → ℝ), D' ⊆ D ∧ IsCompact D' ∧
        μ D ≤ μ D' + ENNReal.ofReal (55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) ∧
        ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ z ∈ D', |f z - g z| ≤ t) ∧
        ∀ z, |g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv (deriv g) z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_geometric_approximation
  refine ⟨C, hC, ?_⟩
  intro N t ζ μ L D f B hN ht ht1 hζ hL hμ hD hDbox hfb hgrid hfits
  let A : Fin (N + 1) → ℝ → ℝ := Fin.cases (fun _ => 0) B
  have hAzero : ∀ z, A 0 z = 0 := fun _ => rfl
  have hAgrid : ∀ k, AffineOnGrid (geometricWidth t N k) (A k) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro m
      exact ⟨0, 0, fun z _ => by simp [A]⟩
    · have hsqrt : Real.sqrt (t ^ (((j : ℝ) + 1) / N)) = geometricWidth t N j.succ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
        unfold geometricWidth
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      simpa only [← hsqrt, A, Fin.cases_succ] using hgrid j
  have hAfit : ∀ k z, z ∈ D → |f z - A k z| ≤ geometricError t N k := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro z hz
      simpa [A, geometricError] using hfb z hz
    · intro z hz
      have hfit := hfits j z hz
      have hp : 0 ≤ t ^ (((j : ℝ) + 1) / N) := Real.rpow_nonneg ht.le _
      simp only [A, Fin.cases_succ, geometricError, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      linarith
  let last : Fin N := ⟨N - 1, by omega⟩
  have hlast : last.succ = Fin.last N := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last, last]
    omega
  have he : ((last : ℝ) + 1) / N = 1 := by
    have hcast : (last : ℝ) + 1 = N := by
      have hh := congrArg Fin.val hlast
      simp only [Fin.val_succ, Fin.val_last] at hh
      exact_mod_cast hh
    rw [hcast, div_self (Nat.cast_ne_zero.mpr hN.ne')]
  have hfinal : ∀ z ∈ D, |f z - A (Fin.last N) z| ≤ t := by
    intro z hz
    rw [← hlast]
    have hb := hfits last z hz
    simpa only [A, Fin.cases_succ, he, Real.rpow_one] using hb
  exact hext N t ζ μ L D f A hN ht ht1 hζ hL hμ hD hDbox hAgrid hAzero hAfit hfinal

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
