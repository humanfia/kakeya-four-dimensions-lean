import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ChartScalar
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarSupport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4FullTimeLayers
open Submission.Obl.k4_subcritical_corrected_scalar_charts

namespace RawChart

/-- A finite list of original child entries gives the exact scalar support
bound for one chart slice. The entry count and slope comparison may be proved
using earlier original witnesses; no mass assumption on a current fibre enters. -/
theorem scalar_support_of_original_entries {α : Type} {ι : Type*} [MeasurableSpace α]
    (C : RawChart α) (b : α → Fin 6 → ℝ) (P : Fin 4 → ℝ)
    (L : ι → Fin 4 → ℝ) (S : Finset ι)
    {D a₀ a₁ t w v χ Ke Mc Md R M d : ℝ}
    (hD : 0 < D) (ha₀ : 0 < a₀) (hw : 0 < w) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hF : C.F t = normalizedRow (liftAffine P v) C.h D a₀ t)
    (hcount : (S.card : ℝ) ≤ M * w ^ (-d))
    (hcoords : ∀ l, (l, t) ∈ C.E → l ∈ C.A ∧
      |b l 0 - (C.q 1 : ℝ) * D| ≤ D ∧ |b l 1 - (C.q 2 : ℝ) * D| ≤ D)
    (hvel : ∀ l, (l, t) ∈ C.E → |b l 3 - v| ≤ χ)
    (hdef : ∀ l, (l, t) ∈ C.E → |b l 4 + b l 0| ≤ χ)
    (hslopes : ∀ i ∈ S, |L i 2| ≤ Mc ∧ |L i 3| ≤ Mc)
    (hdifference : ∀ i ∈ S, |L i 2 - P 2| ≤ Md ∧ |L i 3 - P 3| ≤ Md)
    (hfit : ∀ l, (l, t) ∈ C.E → ∃ i ∈ S,
      |b l 2 + t * b l 5 -
        (L i 0 + L i 1 * t + L i 2 * (b l 0 + t * b l 3) +
          L i 3 * (b l 1 + t * b l 4))| ≤ Ke * a₁)
    (herror : Ke * a₁ + 2 * Mc * χ + 6 * Md * D ≤ a₀ * R * w) :
    ∃ Γ : Finset ℤ, (Γ.card : ℝ) ≤ ((2 * R + 5) * M) * w ^ (-d) ∧
      ∀ l, (l, t) ∈ C.E →
        ⌊FirstJet.scal (C.y b a₀ D) (C.β b a₀ D) (C.γ b a₀ D) C.F l t / w⌋ ∈ Γ := by
  classical
  let center : ι → ℝ := fun i =>
    (predictor (liftAffine (L i) v) t ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D) -
      predictor C.h t ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D)) / a₀
  let Γ := scalarEntryBins w R S center
  have hnear (l : α) (hl : (l, t) ∈ C.E) : ∃ i ∈ S,
      |FirstJet.scal (C.y b a₀ D) (C.β b a₀ D) (C.γ b a₀ D) C.F l t - center i| ≤ R * w := by
    obtain ⟨i, hi, hfit⟩ := hfit l hl
    obtain ⟨hlA, hp, hq⟩ := hcoords l hl
    refine ⟨i, hi, ?_⟩
    rw [C.scalar_eq_original_residual b (liftAffine P v) ha₀.ne' hlA t hF]
    have he := normalizedResidual_original_child_error (L i) P C.h (b l)
      ht hD ha₀ (hvel l hl) (hdef l hl) (hslopes i hi).1 (hslopes i hi).2
      (hdifference i hi).1 (hdifference i hi).2 hp hq hfit
    change |normalizedResidual (liftAffine P v) C.h D a₀ ((C.q 1 : ℝ) * D)
      ((C.q 2 : ℝ) * D) t (b l 0) (b l 1) (b l 2 + t * b l 5) - center i| ≤ _
    exact he.trans ((div_le_div_of_nonneg_right herror ha₀.le).trans_eq (by
      field_simp))
  refine ⟨Γ, ?_, fun l hl => mem_scalarEntryBins hw S center (hnear l hl)⟩
  calc
    _ ≤ (S.card : ℝ) * (2 * R + 5) := card_scalarEntryBins hw hR S center
    _ ≤ (M * w ^ (-d)) * (2 * R + 5) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

end RawChart

end Submission.Obl.k4_horizontal_strict_parameter_step
