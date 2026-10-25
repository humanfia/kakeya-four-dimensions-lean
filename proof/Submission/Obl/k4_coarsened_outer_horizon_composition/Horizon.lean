import Submission.Obl.k4_coarsened_outer_horizon_composition.Interface

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set

set_option linter.unusedVariables false

/-- Once terminal systems at the outer endpoint have short lists at the original
terminal observation, the assumed remainder transfer proves the infimum bound. -/
theorem horizon_of_preparation
    (htransfer : Transfer)
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G)
    {r U : ℝ} (hr : 0 ≤ r) (hrL : r < L)
    (hbound : ∀ N₂ K₂ L₂ d₂ W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂,
      prob N₂ K₂ L₂ d₂ S η W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂ → d₂ ≤ d →
        H N₂ K₂ L₂ W₂ ω₂ ν₂ E₂ B₂ f₂ ≤ U * L₂)
    (hne : {h : ℝ | term N K r W ω ν E B f h}.Nonempty)
    (hprep : ∀ h : ℝ, term N K r W ω ν E B f h → known N K L W ω ν E B f r h) :
    H N K L W ω ν E B f ≤ H N K r W ω ν E B f + U * (L - r) := by
  have hdata := hp
  rcases hdata with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη,
    hformat, hpure, hangular, hreg, htyp, hcap, hang⟩
  have hlower : H N K L W ω ν E B f - U * (L - r) ≤ H N K r W ω ν E B f := by
    apply le_csInf hne
    intro h hh
    obtain ⟨N₂, K₂, W₂, ω₂, ν₂, E₂, P₂, B₂, f₂, g₂, G₂, hp₂, hcomp⟩ :=
      htransfer N K L d S η W ω ν E P B f g G hp r h d hr hrL hd hd1
        (fun s hrs hsL => hcap s (hr.trans hrs) hsL) (hprep h hh)
    have hb := hbound N₂ K₂ (L - r) d W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂ hp₂ le_rfl
    linarith
  linarith

end Submission.Obl.k4_coarsened_outer_horizon_composition
