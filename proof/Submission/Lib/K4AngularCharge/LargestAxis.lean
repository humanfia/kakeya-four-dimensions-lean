/- Adapted from: here:o107 (session x0359, branch x0359-libcharge, commit dbbe0acd). -/
import Mathlib
import Submission.Lib.K4AngularCharge.LevelMass
import Submission.Lib.K4AngularCharge.ChartCells

/-!
# Fullness of the largest axis (paper Lemma a01:largest-axis) for X path levels

A chart whose largest axis is deficient, `Σ|Q| ≤ ρ κ / 2^T` with `ρ` small, confines the
velocities of its lines to a ball of radius `2 κ² ρ`, hence to at most `(4 κ² ρ / ε + 4)²` cells
of width `ε` (`gchart_cells_deficient`). With `level_mass_le_coarse` (lists read at any depth
`r ≤ L` through the terminal observation) the deficient charts of a path level carry at most
`κ (4 κ² ρ / ε + 4)² (α / β)` of the incidence mass outside the typicality exceptions; with
`ε = δ(N, u)`, `ρ ≤ N^(-u)`, `α / β = N^(-S u + 2 τ')` this is power-small for every `S > 0`,
which is the pruning used in paper Prop. 4.7 (spatial fullness of descendants) and Section 3.
-/

namespace Submission.Lib.K4AngularCharge

open Submission.Lib.K4XInterface

open MeasureTheory

open scoped ENNReal

/-- Velocity cells of a chart whose largest axis is deficient: if `Σ|Q| ≤ ρ κ / 2^T`, the
velocities of its lines meet at most `(4 κ² ρ / ε + 4)²` cells of side `ε`. -/
theorem gchart_cells_deficient {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hdef : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ ρ * κ / (2 : ℝ) ^ T) (hε : 0 < ε)
    (hκ : 0 ≤ κ) :
    ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ (4 * κ ^ 2 * ρ / ε + 4) ^ 2 ∧
      ∀ l ∈ A, (fun j => ⌊(gv l) j / ε⌋) ∈ V := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  set s := ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| with hs
  have hdetle : |Q.det| ≤ s ^ 2 := by
    rw [Matrix.det_fin_two, hs]
    simp only [Fin.sum_univ_two]
    have := abs_sub (Q 0 0 * Q 1 1) (Q 0 1 * Q 1 0)
    rw [abs_mul, abs_mul] at this
    nlinarith [abs_nonneg (Q 0 0), abs_nonneg (Q 0 1), abs_nonneg (Q 1 0), abs_nonneg (Q 1 1)]
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨V, hV, hmem⟩ := frame_cells Q h.1 u (ρ := 2 * κ * (2 : ℝ) ^ T) (σ₁ := s) (θ := s ^ 2)
    hε (by positivity) le_rfl hdetle
  refine ⟨V, hV.trans ?_, fun l hl => hmem _ (gchart_velocity h hl)⟩
  rw [Real.sqrt_sq hs0]
  have hb : 2 * (2 * κ * (2 : ℝ) ^ T * s) / ε ≤ 4 * κ ^ 2 * ρ / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have : (2 : ℝ) ^ T * s ≤ ρ * κ := by
      rw [le_div_iff₀ h2] at hdef; linarith
    nlinarith
  have hpos : 0 ≤ 2 * (2 * κ * (2 : ℝ) ^ T * s) / ε := by positivity
  calc (2 * (2 * κ * (2 : ℝ) ^ T * s) / ε + 2) * (2 * (2 * κ * (2 : ℝ) ^ T * s) / ε + 4)
      ≤ (4 * κ ^ 2 * ρ / ε + 4) * (4 * κ ^ 2 * ρ / ε + 4) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = (4 * κ ^ 2 * ρ / ε + 4) ^ 2 := by ring

end Submission.Lib.K4AngularCharge

namespace Submission.Lib.K4AngularCharge

open Submission.Lib.K4XInterface

open MeasureTheory

open scoped ENNReal

/-- `level_mass_le` for charts whose lists read the observation at a coarser depth `r ≤ L`. -/
theorem level_mass_le_coarse {W C : ℕ} (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    [hν : ∀ γ, IsProbabilityMeasure (ν γ)] (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hE : ∀ γ, E γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (B : Fin W → ℝ) {N r L : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrL : r ≤ L) (u : ℝ)
    (g : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hg : ∀ γ, Measurable (g γ))
    (hmap : ∀ γ, Measure.map (gobs (B γ) (gδ N L)) (((ν γ).prod volume).restrict (E γ)) =
      (volume.prod Measure.count).withDensity (g γ))
    (G : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞)
    (hG : ∀ γ, Measurable (G γ))
    (hmapG : ∀ γ, Measure.map (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
        (gobs (B γ) (gδ N L) p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋))
          (((ν γ).prod volume).restrict (E γ)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (G γ))
    (γb : Fin C → Fin W) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hF : ∀ b, MeasurableSet (F b)) (hFE : ∀ b, F b ⊆ E (γb b))
    (lst : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → Finset (Fin C))
    (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (γb b) (gobs (B (γb b)) (gδ N r) p)) (κ : ℕ)
    (hκ : ∀ γ o, (lst γ o).card ≤ κ) (V : Fin C → Finset (Fin 2 → ℤ))
    (hV : ∀ b, ∀ p ∈ F b, (fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∈ V b) (M : ℕ)
    (hM : ∀ b, (V b).card ≤ M) (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    ∑ b, ENNReal.ofReal (ω (γb b)) * ((ν (γb b)).prod volume) (F b) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) *
          ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) Set.univ +
        κ * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ))
          {p | α < G γ (gobs (B γ) (gδ N L) p, fun j : Fin 2 => ⌊(gv p.1) j / u⌋) ∨
            g γ (gobs (B γ) (gδ N L) p) < β} := by
  set n := depthIdx N L -
    depthIdx N r
  exact level_mass_le ω ν E hE B (gδ N L) u g hg hmap G hG hmapG γb F hF hFE
    (fun γ o => lst γ (coarsenObs n o))
    (fun b p hp => by
      have := hlst b p hp
      rwa [gobs_coarsen hN hr hrL] at this)
    κ (fun γ o => hκ γ (coarsenObs n o)) V hV M hM α β hβ

end Submission.Lib.K4AngularCharge
