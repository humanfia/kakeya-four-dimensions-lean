-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.OriginalNativeCenters, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/OriginalNativeCenters.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/OriginalNativeCenters.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalNativeCenters.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalNativeCenters.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DiscriminantPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GoodBaseCenters

/-! # Original-law heavy entries supply uniformly many good branch centers -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- A full ORIGINAL entry floor and original base cap control the native
discriminant and give a net of GOOD centers at any prescribed power
radius. Both the coefficient exponent and the net exponent are independent
of the input format; no conditional probability normalization is used. -/
theorem original_native_discriminant_centers (q : ℕ) :
    ∃ e : ℕ, 4 ≤ e ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (w : Ω → ℝ)
      (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ K a : ℝ, 2 ≤ K → 0 < a → |curvature P 3| ≤ K / a →
      |curvature P 3| ≤ (K ^ 5 * a)⁻¹ →
      ENNReal.ofReal ((K ^ q)⁻¹) ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal (K ^ q) * volume U) →
      (∀ᵐ x ∂μ, Z x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
        |eval (Fin.snoc (Z x) (w x)) P| ≤ K * a ∧
        K⁻¹ ≤ |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ∧
        |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ≤ K) →
      (∀ d, |(baseDiscriminant P).coeff d| ≤ K ^ e) ∧
      ∀ R : ℕ, ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
        (S.card : ℝ) ≤ K ^ (3 * R + 12) ∧
        (∀ c ∈ S, (fun j => c j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
          ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => c j) (baseDiscriminant P)) ∧
        ∀ᵐ x ∂μ, ∃ c ∈ S, ‖WithLp.toLp 2 (Z x) - c‖ ≤ (K ^ R)⁻¹ := by
  obtain ⟨e, he, hprep⟩ := original_native_discriminant_preparation q
  refine ⟨e, he, ?_⟩
  intro Ω _ μ Z w P hP K a hK ha hcurv hsmall hmass hdom hae
  obtain ⟨hcoeff, hgood⟩ := hprep μ Z w P hP K a hK ha hcurv hsmall hmass hdom hae
  refine ⟨hcoeff, ?_⟩
  intro R
  let A : Set (EuclideanSpace ℝ (Fin 3)) := {z |
    (fun j => z j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => z j) (baseDiscriminant P)}
  have hA (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ A) (j : Fin 3) : |z j| ≤ 1 := by
    rw [abs_of_nonneg (hz.1.1 j)]
    exact hz.1.2 j
  obtain ⟨S, hcard, hsub, hcover⟩ := original_good_base_centers_power R hK A hA
  refine ⟨S, hcard, hsub, ?_⟩
  filter_upwards [hae, hgood] with x hx hgoodx
  exact hcover (WithLp.toLp 2 (Z x)) ⟨hx.1, hgoodx⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
