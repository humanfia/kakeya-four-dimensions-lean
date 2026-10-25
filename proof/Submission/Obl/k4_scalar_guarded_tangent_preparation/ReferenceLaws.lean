import Submission.Obl.k4_scalar_guarded_tangent_preparation.Interface

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

noncomputable section

/-- The original pure observation, before binning either base coordinate. -/
def pureObservation (N s : ℝ) (z : Incidence) : (Fin 2 → ℝ) × ℤ :=
  (![z.2, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y z.1 z.2],
    hiddenBin N s z)

/-- Input to the finite-law preparation. The reference laws, palettes and
finite codes are all fixed before likelihood deletion. `Y` records the tested
base/hidden grid cells and `Z` the finest velocity cell. The information budget
is measured with the original weights and unnormalized atom masses. -/
def ReferenceLaws (N B : ℕ → ℝ) (d S : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (σ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Incidence) : Prop :=
  (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
  (∀ k, 1 ≤ B k) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, B k ≤ N k ^ ε) ∧
  0 ≤ d ∧ d < 1 ∧ 0 < S ∧ S ≤ 1 ∧
  (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧
    ∀ g, σ k g Set.univ ≤ 1) ∧
  ∃ (m : ℕ → ℕ) (n : (k : ℕ) → Fin (W k) → ℕ)
    (X : (k : ℕ) → (g : Fin (W k)) → Incidence → Fin (n k g))
    (Y : (k : ℕ) → (g : Fin (W k)) → Fin (n k g) → ℕ)
    (Z : (k : ℕ) → (g : Fin (W k)) → Fin (n k g) → ℤ)
    (q : (k : ℕ) → Fin (W k) → Fin (m k ^ 2 + 1) → ℕ → Fin 2 → ℤ)
    (c : (k : ℕ) → Fin (W k) → Fin (m k ^ 2 + 1) → ℕ → ℤ)
    (α : ℕ → ℝ)
    (π₀ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ),
  (∀ k, 1 ≤ m k) ∧
  Filter.Tendsto (fun k => (m k : ℝ)) Filter.atTop Filter.atTop ∧
  (∀ k, 0 < α k ∧ 2 ≤ N k ^ α k) ∧
  Filter.Tendsto α Filter.atTop (nhds 0) ∧
  (∀ k g, Measurable (X k g) ∧ MeasureTheory.IsProbabilityMeasure (π₀ k g) ∧
    MeasureTheory.Measure.map (fun z : Incidence => z.1.2 1) (σ k g) =
      (σ k g Set.univ) • π₀ k g ∧
    (∀ᵐ z ∂σ k g,
      Z k g (X k g z) = velocityBin (N k) (m k : ℝ) (z.1.2 1) ∧
      ∀ j : Fin (m k ^ 2 + 1),
        baseBin (N k) ((j : ℝ) / (m k : ℝ)) z = q k g j (Y k g (X k g z)) ∧
        hiddenBin (N k) ((j : ℝ) / (m k : ℝ)) z = c k g j (Y k g (X k g z))) ∧
    ∀ j : Fin (m k ^ 2 + 1),
      MeasureTheory.Measure.map (pureObservation (N k) ((j : ℝ) / (m k : ℝ)))
          (σ k g) ≤
        ENNReal.ofReal (B k * N k ^ (-d * ((j : ℝ) / (m k : ℝ)))) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (b : ℝ),
    R⁻¹ ≤ b → b ≤ R → ∀ e : ℤ,
      π₀ k g {v | velocityBin (N k) b v = e} ≤
        ENNReal.ofReal (B k * N k ^ (-S * b))) ∧
  (∀ k,
    (∑ g : Fin (W k), ω k g *
      ∑ i : Fin (n k g),
        (σ k g {z | X k g z = i}).toReal *
          max 0 (Real.log
            (((σ k g {z | Y k g (X k g z) = Y k g i ∧
                Z k g (X k g z) = Z k g i}).toReal * (σ k g Set.univ).toReal) /
              ((σ k g {z | Y k g (X k g z) = Y k g i}).toReal *
                (σ k g {z | Z k g (X k g z) = Z k g i}).toReal)))) ≤
      ((∑ g : Fin (W k), ENNReal.ofReal (ω k g) * σ k g Set.univ).toReal / 2) *
        Real.log (N k ^ α k))

/-- All-real rectangular bounds on the current submeasure, with one fixed
palette in each world. They persist under further incidence restriction. -/
def RectangularCaps (N K : ℕ → ℝ) (d S : ℝ) (W : ℕ → ℕ)
    (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Incidence)
    (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
  (∀ k g, MeasureTheory.IsProbabilityMeasure (π k g)) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
    R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, π k g {v | velocityBin (N k) b v = c} ≤
      ENNReal.ofReal (K k * N k ^ (-S * b))) ∧
    (∀ (q : Fin 2 → ℤ) (c : ℤ), ρ k g
      {z | baseBin (N k) r z = q ∧ hiddenBin (N k) s z = c} ≤
      ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧
    (∀ (q : Fin 2 → ℤ) (c e : ℤ), ρ k g
      {z | baseBin (N k) r z = q ∧ hiddenBin (N k) s z = c ∧
        velocityBin (N k) b (z.1.2 1) = e} ≤
      ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
        π k g {v | velocityBin (N k) b v = e}))

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
