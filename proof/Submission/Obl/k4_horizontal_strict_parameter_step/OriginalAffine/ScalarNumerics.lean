import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ScalarSupport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4FullTimeLayers

namespace RawChart

/-- The strict transverse gap and the original contact budget pay both error
terms in scalar restoration, uniformly over every child width. -/
theorem scalar_support_with_native_budgets {α : Type} {ι : Type*} [MeasurableSpace α]
    (C : RawChart α) (b : α → Fin 6 → ℝ) (P : Fin 4 → ℝ)
    (L : ι → Fin 4 → ℝ) (S : Finset ι)
    {D a₀ t w v χ K q d : ℝ}
    (hK : 1 ≤ K) (hD : 0 < D) (ha₀ : 0 < a₀) (hw : 0 < w) (hq : 0 < q)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hF : C.F t = normalizedRow (liftAffine P v) C.h D a₀ t)
    (hcount : (S.card : ℝ) ≤ 73728 * K ^ 11 * w ^ (-d))
    (hcoords : ∀ l, (l, t) ∈ C.E → l ∈ C.A ∧
      |b l 0 - (C.q 1 : ℝ) * D| ≤ D ∧ |b l 1 - (C.q 2 : ℝ) * D| ≤ D)
    (hvel : ∀ l, (l, t) ∈ C.E → |b l 3 - v| ≤ χ)
    (hdef : ∀ l, (l, t) ∈ C.E → |b l 4 + b l 0| ≤ χ)
    (hslopes : ∀ i ∈ S, |L i 2| ≤ 8 * K ^ 4 ∧ |L i 3| ≤ 8 * K ^ 4)
    (hdifference : ∀ i ∈ S,
      |L i 2 - P 2| ≤ 2359296 * K ^ 10 * a₀ / q ^ 2 ∧
      |L i 3 - P 3| ≤ 2359296 * K ^ 10 * a₀ / q ^ 2)
    (hfit : ∀ l, (l, t) ∈ C.E → ∃ i ∈ S,
      |b l 2 + t * b l 5 -
        (L i 0 + L i 1 * t + L i 2 * (b l 0 + t * b l 3) +
          L i 3 * (b l 1 + t * b l 4))| ≤ K * (a₀ * w))
    (hcontact : 16 * K ^ 4 * χ ≤ a₀ * w)
    (hroom : 14155776 * K ^ 10 * D ≤ w * q ^ 2) :
    ∃ Γ : Finset ℤ, (Γ.card : ℝ) ≤ 811008 * K ^ 12 * w ^ (-d) ∧
      ∀ l, (l, t) ∈ C.E →
        ⌊FirstJet.scal (C.y b a₀ D) (C.β b a₀ D) (C.γ b a₀ D) C.F l t / w⌋ ∈ Γ := by
  have hK0 : 0 ≤ K := by linarith
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hspatial : 6 * (2359296 * K ^ 10 * a₀ / q ^ 2) * D ≤ a₀ * w := by
    calc
      _ = a₀ * ((14155776 * K ^ 10 * D) / q ^ 2) := by ring
      _ ≤ a₀ * w := mul_le_mul_of_nonneg_left ((div_le_iff₀ hq2).mpr hroom) ha₀.le
  have herror : K * (a₀ * w) + 2 * (8 * K ^ 4) * χ +
      6 * (2359296 * K ^ 10 * a₀ / q ^ 2) * D ≤ a₀ * (K + 2) * w := by
    nlinarith
  obtain ⟨Γ, hΓ, hcover⟩ := C.scalar_support_of_original_entries b P L S hD ha₀ hw
    (by linarith : 0 ≤ K + 2) ht hF hcount hcoords hvel hdef hslopes hdifference hfit herror
  refine ⟨Γ, hΓ.trans ?_, hcover⟩
  have hconst : (2 * (K + 2) + 5) * (73728 * K ^ 11) ≤ 811008 * K ^ 12 := by
    calc
      _ ≤ (11 * K) * (73728 * K ^ 11) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hw.le _)

end RawChart

end Submission.Obl.k4_horizontal_strict_parameter_step
