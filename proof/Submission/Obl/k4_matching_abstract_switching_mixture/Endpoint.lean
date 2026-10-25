import Mathlib

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Set MeasureTheory
open scoped ENNReal

/-- The normalized switching endpoint map. -/
noncomputable def endpoint {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ : ℝ)
    (x : ℝ × (Fin m → ℝ)) : ℝ × (Fin m → ℝ) :=
  (x.1, fun j => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) +
    ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) /
    (((j : ℕ) + 1).factorial : ℝ))

/-- The time domain appearing in the mixture certificate. -/
def timeDomain {m : ℕ} (L : ℝ) (x : ℝ × (Fin m → ℝ)) : Prop :=
  |x.1| ≤ 1 ∧ (∀ p : Fin m, |x.2 p| ≤ 1) ∧
    ∀ p r : Fin m, p ≠ r → L⁻¹ ≤ |x.2 p - x.2 r|

/-- A separated endpoint pullback. -/
def pullback {m : ℕ} (L : ℝ) (U : Fin (m + 1) → ℝ) (s₀ : ℝ)
    (T : Set (ℝ × (Fin m → ℝ))) : Set (ℝ × (Fin m → ℝ)) :=
  {x | timeDomain L x ∧ endpoint U s₀ x ∈ T}

theorem volume_pullback_ne_top {m : ℕ} (L : ℝ) (U : Fin (m + 1) → ℝ) (s₀ : ℝ)
    (T : Set (ℝ × (Fin m → ℝ))) : volume (pullback L U s₀ T) ≠ ∞ := by
  apply ne_of_lt
  apply measure_lt_top_of_subset (s :=
    Icc (-1 : ℝ) 1 ×ˢ Set.pi univ (fun _ : Fin m => Icc (-1 : ℝ) 1))
  · intro x hx
    exact ⟨abs_le.mp hx.1.1, fun p _ => abs_le.mp (hx.1.2.1 p)⟩
  · exact ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).prod
      (isCompact_univ_pi fun _ : Fin m => isCompact_Icc)).measure_lt_top.ne

end Submission.Obl.k4_matching_abstract_switching_mixture
