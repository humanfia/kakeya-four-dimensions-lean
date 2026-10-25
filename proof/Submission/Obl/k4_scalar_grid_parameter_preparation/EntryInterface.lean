import Submission.Obl.k4_scalar_grid_parameter_preparation.FrozenAdapters

/-!
# The interface of the coefficient-entry stage

`EntryStageClaim` is what the final assembly takes from the entry pruning: from a mask `B` with
bounded coefficients, density `ρ|B ≤ Hc θ dt`, pointwise coefficient floors on a finite scale set
`Ξ k` and the joint caps, a submask `E` losing at most `1 / (100 K)` with coefficient lists of
subpower size at every scale of `Ξ k` in each compact range. Nothing is proved about it here.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

/-- The interface of the coefficient-entry stage of the preparation. -/
def EntryStageClaim : Prop :=
  ∀ (N K Hc : ℕ → ℝ) (W : ℕ → ℕ) (d : ℝ)
    (θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (Ξ : ℕ → Finset ℝ)
    (B : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
    (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K → Subpower N Hc → 0 ≤ d → d < 1 →
    (∀ k g, IsFiniteMeasure (ρ k g)) → (∀ k g, θ k g Set.univ ≤ 1) →
    (∀ k g, IsProbabilityMeasure (π k g)) →
    (∀ᶠ k in atTop, ((Ξ k).card : ℝ) ≤ Hc k) → (∀ k, ∀ r ∈ Ξ k, 0 < r) →
    (∀ k g, MeasurableSet (B k g) ∧
      ∀ p ∈ B k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ Hc k) →
    (∀ k g, (ρ k g).restrict (B k g) ≤ ENNReal.ofReal (Hc k) • (θ k g).prod volume) →
    (∀ k g, ∀ r ∈ Ξ k, ∀ z ∈ B k g,
      ENNReal.ofReal (N k ^ (-((1 + d) * r)) / Hc k) *
          π k g (velBin (N k) r ⌊z.1.2 1 / N k ^ (-r)⌋) ≤
        θ k g {l | coeffTag (N k) r l = coeffTag (N k) r z.1}) →
    (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ), R⁻¹ ≤ r → r ≤ R →
      ∀ (q : Fin 3 → ℤ) (c : ℤ),
        ρ k g {p | physTag (N k) r p = q ∧ (⌊p.1.2 1 / (N k ^ (-r))⌋ : ℤ) = c} ≤
          ENNReal.ofReal (Hc k * N k ^ (-((2 + d) * r))) * π k g (velBin (N k) r c)) →
    ∃ (Hl : ℕ → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
      Subpower N Hl ∧ (∀ k g, MeasurableSet (E k g) ∧ E k g ⊆ B k g) ∧
      (∀ᶠ k in atTop, ∀ g, ρ k g (B k g \ E k g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)), ∀ r ∈ Ξ k, R⁻¹ ≤ r → r ≤ R →
        ∀ (q : Fin 3 → ℤ) (c : ℤ),
          ({b : Fin 5 → ℤ | (ρ k g).restrict (E k g) {p | physTag (N k) r p = q ∧
            (⌊p.1.2 1 / (N k ^ (-r))⌋ : ℤ) = c ∧ coeffTag (N k) r p.1 = b} ≠ 0}.ncard : ℝ) ≤
            Hl k

/-- The frozen joint cap at `r = s = b`, read on physical cubes and velocity bins. -/
theorem frozen_joint_physical {N K : ℕ → ℝ} {d S : ℝ} {W : ℕ → ℕ}
    {ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {π : (k : ℕ) → Fin (W k) → Measure ℝ} (hcaps : FrozenCaps N K d S W ρ π) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ), R⁻¹ ≤ r → r ≤ R →
      ∀ (q : Fin 3 → ℤ) (c : ℤ),
        ρ k g {p | physTag (N k) r p = q ∧ (⌊p.1.2 1 / (N k ^ (-r))⌋ : ℤ) = c} ≤
          ENNReal.ofReal (K k * N k ^ (-((2 + d) * r))) * π k g (velBin (N k) r c) := by
  intro R hR
  filter_upwards [hcaps R hR] with k hk
  intro g r hr1 hr2 q c
  have hexp : -((2 + d) * r) = -2 * r - d * r := by ring
  rw [hexp]
  refine le_trans (measure_mono ?_) ((hk g r r r hr1 hr2 hr1 hr2 hr1 hr2).2.2 ![q 0, q 1] (q 2) c)
  rintro p ⟨hp, hc⟩
  refine ⟨?_, ?_, hc⟩
  · funext e
    fin_cases e
    · exact congrFun hp 0
    · exact congrFun hp 1
  · exact congrFun hp 2

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
