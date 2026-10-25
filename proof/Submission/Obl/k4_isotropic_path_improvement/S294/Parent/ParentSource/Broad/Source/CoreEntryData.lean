-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreEntryData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreEntryData.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreEntryData.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCoreEntries

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

/-- Named data for the coherent original core family. The raw entries
and their earlier floors remain available after later selections. -/
structure CoreEntryData {Ω : Type*} [MeasurableSpace Ω]
    (e R : ℕ) (K : ℝ) (P : Poly) (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 4)) (G : Set Ω) (θ : ENNReal) where
  codes : Finset (Fin 3 → ℤ)
  center : (Fin 3 → ℤ) → Base
  extension : (↥codes × Bool) → EuclideanSpace ℂ (Fin 3) → ℂ
  sheet : (↥codes × Bool) → Base → ℝ
  raw : (↥codes × Bool) → Set Ω
  kept : (↥codes × Bool) → Set Ω
  count_le : (codes.card : ℝ) ≤ K ^ (3 * R + 18)
  centers : ∀ c ∈ codes, (fun j => center c j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
    ((K ^ e)⁻¹) ^ 2 ≤ MvPolynomial.eval (fun j => center c j) (baseDiscriminant P) ∧
      ∀ j, ⌊center c j / ((K ^ R)⁻¹ / 12)⌋ = c j
  measurable : ∀ i, MeasurableSet (raw i) ∧ MeasurableSet (kept i)
  disjoint : Pairwise (fun i j => Disjoint (kept i) (kept j))
  subset : ∀ i, kept i ⊆ raw i ∧ raw i ⊆ G
  branch : ∀ i, (raw i).Nonempty →
    LocalNativeBranchData 5186 P (fun j => center i.1.1 j)
      (K ^ R)⁻¹ (nativeCoreSign i.2) (extension i) (sheet i)
  points : ∀ i p, p ∈ raw i →
    ‖(K ^ R) • (nativeBase (X p) - center i.1.1)‖ ≤ 1 / 4 ∧
      0 < value (MvPolynomial.pderiv 3 P) (rootLift P (X p)) * nativeCoreSign i.2 ∧
      rootLift P (X p) 3 = sheet i ((K ^ R) • (nativeBase (X p) - center i.1.1))
  original_floor : ∀ i, (kept i).Nonempty → θ ≤ μ (raw i)
  loss : μ (⋃ i, kept i)ᶜ ≤ ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ

theorem coreEntryData_of_family {Ω : Type*} [MeasurableSpace Ω]
    {e R : ℕ} {K : ℝ} {P : Poly} {μ : Measure Ω}
    {X : Ω → EuclideanSpace ℝ (Fin 4)} {G : Set Ω} {θ : ENNReal}
    (h : NativeCoreEntryFamily e R K P μ X G θ) :
    Nonempty (CoreEntryData e R K P μ X G θ) := by
  obtain ⟨codes, c, F, f, U, V, hcard, hc, hm, hd, hs, hb, hp, hf, hl⟩ := h
  exact ⟨⟨codes, c, F, f, U, V, hcard, hc, hm, hd, hs, hb, hp, hf, hl⟩⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
