import Submission.Obl.k4_homogeneous_native_pair_preparation.ProblemCaps
import Submission.Obl.k4_homogeneous_native_pair_preparation.NativeGood

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- A single mask imposes all density caps and the native regularity conditions.
Its exceptional mass is measured under the original selected incidence laws. -/
theorem problem_good_masks (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hp : prob N K L d S η W ω ν E P B f g G)
    (depths : Finset ℝ) (hr : ∀ r ∈ depths, 0 ≤ r ∧ r ≤ L)
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (huL : u ≤ η * L) :
    ∃ Good : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ k γ, MeasurableSet (Good k γ) ∧ Good k γ ⊆ E k γ ∧
        ∀ p ∈ Good k γ,
          ‖y p.1 p.2‖ + ‖v p.1‖ ≤ K k ∧
          |MvPolynomial.eval (x p.1 p.2) (P k γ)| ≤ K k ∧
          B k γ / K k ≤
            |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ∧
          (∀ r ∈ depths, g k γ r (obs (B k γ) (δ (N k) r) p) ≤
            ENNReal.ofReal (N k ^ (-f r + a))) ∧
          G k γ u (obs (B k γ) (δ (N k) L) p,
            fun j : Fin 2 => ⌊v p.1 j / δ (N k) u⌋) ≤
              ENNReal.ofReal (N k ^ (-f L - S * u + a))) ∧
      IsPowerSmall N (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
        (((ν k γ).prod volume).restrict (E k γ)) (Good k γ)ᶜ) := by
  classical
  obtain ⟨Raw, hRE, hRm, hRp, hRa, hRt⟩ :=
    problem_pure_and_angular_caps N K L d S η W ω ν E P B f g G hp depths hr ha hu huL
  obtain ⟨_, _, _, _, _, _, _, _, ⟨Mp, Dp, hworld⟩, _⟩ := hp
  have hex (k : ℕ) (γ : Fin (W k)) :
      ∃ F, F ⊆ Raw k γ ∧ MeasurableSet F ∧
        (∀ p ∈ F, NativeIncidenceGood (K k) (B k γ) (P k γ) p) ∧
        (((ν k γ).prod volume).restrict (E k γ)) Fᶜ =
          (((ν k γ).prod volume).restrict (E k γ)) (Raw k γ)ᶜ := by
    obtain ⟨hν, _, _, _, _, _, _, hEm, hEt, _, _, hupper, hfloor⟩ :=
      (hworld k).2.2.2.1 γ
    letI : IsProbabilityMeasure (ν k γ) := hν
    exact native_pointwise_submask (ν k γ) (E k γ) hEm hEt (K k) (B k γ) (P k γ)
      hupper hfloor (Raw k γ) (hRm k γ)
  choose Good hsub hmeas hnative hmass using hex
  refine ⟨Good, ?_, ?_⟩
  · intro k γ
    refine ⟨hmeas k γ, (hsub k γ).trans (hRE k γ), ?_⟩
    intro p hpG
    obtain ⟨hP, hder, hyv⟩ := hnative k γ p hpG
    exact ⟨hyv, hP, hder, hRp k γ p (hsub k γ hpG), hRa k γ p (hsub k γ hpG)⟩
  · simpa only [hmass] using hRt

end Submission.Obl.k4_homogeneous_native_pair_preparation
