-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.OriginalNativeBranches, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/OriginalNativeBranches.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/OriginalNativeBranches.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalNativeBranches.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalNativeBranches.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeBranch
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GoodCoreLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.QuarterCoreGeometry

/-! # Coded quarter-core branches from an original heavy native entry -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- An actual finite coded branch family at one common native radius. -/
def NativeQuarterBranchCover {Ω : Type*} [MeasurableSpace Ω]
    (e R : ℕ) (K : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) : Prop :=
  ∃ codes : Finset (Fin 3 → ℤ),
  ∃ center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3),
    (codes.card : ℝ) ≤ K ^ (3 * R + 18) ∧
    (∀ i ∈ codes,
      (fun j => center i j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => center i j) (baseDiscriminant P) ∧
      (∀ j, ⌊center i j / ((K ^ R)⁻¹ / 12)⌋ = i j) ∧
      ∀ σ : ℝ, σ ≠ 0 →
        (curvature P 3 = 0 → 0 < eval (fun j => center i j)
          (restrictBase (pderiv 3 P)) * σ) →
        LocalNativeBranch 5186 P (fun j => center i j) (K ^ R)⁻¹ σ) ∧
    ∀ᵐ p ∂μ, ∃ i ∈ codes,
      ‖(K ^ R) • (WithLp.toLp 2 (Z p) - center i)‖ ≤ 1 / 4

/-- An ORIGINAL unnormalized heavy entry provides an entire coded family
of local signed branches. The relation degree is fixed, and the height
and radius exponents precede every equation, source and format datum.
Centers retain their actual grid codes for bounded reference menus.
No common intercept or later selected-entry floor occurs here. -/
theorem original_native_quarter_branch_cover (q : ℕ) :
    ∃ e R : ℕ, 4 ≤ e ∧ 1 ≤ R ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (w : Ω → ℝ)
      (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
    ∀ K a : ℝ, 2 ≤ K → 0 < a → |curvature P 3| ≤ K / a →
      |curvature P 3| ≤ (K ^ 5 * a)⁻¹ →
      ENNReal.ofReal ((K ^ q)⁻¹) ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal (K ^ q) * volume U) →
      (∀ᵐ p ∂μ, Z p ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
        |eval (Fin.snoc (Z p) (w p)) P| ≤ K * a ∧
        K⁻¹ ≤ |eval (Fin.snoc (Z p) (w p)) (pderiv 3 P)| ∧
        |eval (Fin.snoc (Z p) (w p)) (pderiv 3 P)| ≤ K) →
      NativeQuarterBranchCover e R K P μ Z := by
  obtain ⟨e, he, hprep⟩ := original_native_discriminant_preparation q
  obtain ⟨E, hE, hbranch⟩ := uniform_centered_native_branch
  let R := e * E
  refine ⟨e, R, he, by dsimp only [R]; nlinarith, ?_⟩
  intro Ω _ μ Z w P hP K a hK ha hcurv hsmall hmass hcap hae
  obtain ⟨hcoeff, hgood⟩ := hprep μ Z w P hP K a hK ha hcurv hsmall hmass hcap hae
  let Good : Set (EuclideanSpace ℝ (Fin 3)) := {z |
    (fun j => z j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => z j) (baseDiscriminant P)}
  have hGood (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ Good) (j : Fin 3) : |z j| ≤ 1 := by
    rw [abs_of_nonneg (hz.1.1 j)]
    exact hz.1.2 j
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKR : K ^ R ≠ 0 := (pow_pos hKp R).ne'
  obtain ⟨codes, center, hcard, hcenters, hcover⟩ :=
    original_good_base_centers_with_codes Good hGood (show 0 < (K ^ R)⁻¹ / 4 by positivity)
  have hside : 12 / ((K ^ R)⁻¹ / 4) + 2 ≤ K ^ (R + 6) := by
    calc
      _ = 48 * K ^ R + 2 := by field_simp; ring
      _ ≤ 50 * K ^ R := by have hh := one_le_pow₀ hK1 (n := R); linarith
      _ ≤ K ^ 6 * K ^ R := mul_le_mul_of_nonneg_right
        ((by norm_num : (50 : ℝ) ≤ 2 ^ 6).trans (pow_le_pow_left₀ (by norm_num) hK 6))
        (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hKA : 2 ≤ K ^ e := hK.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ K) (by omega : 1 ≤ e))
  refine ⟨codes, center, ?_, ?_, ?_⟩
  · calc
      _ ≤ (12 / ((K ^ R)⁻¹ / 4) + 2) ^ 3 := hcard
      _ ≤ (K ^ (R + 6)) ^ 3 := pow_le_pow_left₀ (by positivity) hside 3
      _ = _ := by rw [← pow_mul]; congr 1; omega
  · intro i hi
    obtain ⟨hc, hcode⟩ := hcenters i hi
    have hmesh : ((K ^ R)⁻¹ / 4) / 3 = (K ^ R)⁻¹ / 12 := by ring
    refine ⟨hc.1, hc.2, (fun j => by simpa only [hmesh] using hcode j), ?_⟩
    intro σ hσ hσ0
    have hh := hbranch (K ^ e) hKA P hP (fun j => center i j)
      (hGood _ hc) hcoeff hc.2 σ hσ hσ0
    simpa only [← pow_mul, R] using hh
  · filter_upwards [hae, hgood] with p hp hgp
    obtain ⟨i, hi, hnear⟩ := hcover (WithLp.toLp 2 (Z p)) ⟨hp.1, hgp⟩
    refine ⟨i, hi, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hKp R)]
    calc
      _ ≤ K ^ R * ((K ^ R)⁻¹ / 4) := mul_le_mul_of_nonneg_left hnear (by positivity)
      _ = 1 / 4 := by field_simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
