import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set Filter

/-- The exact per-packet conjunction of the frozen conclusion. -/
noncomputable def PacketConclusion (data : Data) (k : ℕ) (i : Fin (data.n k 1))
    (μ : Measure Incidence) (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (H : ℝ) (D : ℕ) (Z B R : ℝ) : Prop :=
  let h := packetLength data k
  MeasurableSet (data.A k 1 i) ∧
    MeasureTheory.IsProbabilityMeasure (data.ν k (data.γ k 1 i)) ∧
    MeasureTheory.IsProbabilityMeasure (data.π k (data.γ k 1 i)) ∧
    (∀ᵐ l ∂data.ν k (data.γ k 1 i), ∀ e, |l.2 e| ≤ H) ∧
    data.N k ^ (-data.κ) / H ≤ h ∧
    h ≤ H * data.N k ^ (-data.κ) ∧
    0 < h ∧
    h ≤ 1 ∧
    ENNReal.ofReal (data.N k ^ (-data.d) * h / H) ≤ data.ν k (data.γ k 1 i) (data.A k 1 i) ∧
    data.ν k (data.γ k 1 i) (data.A k 1 i) ≤ ENNReal.ofReal (H * data.N k ^ (-data.d) * h) ∧
    μ ≤ data.ρ k (data.γ k 1 i) ∧
    μ ≤ ENNReal.ofReal (H) • ((data.ν k (data.γ k 1 i)).prod MeasureTheory.volume) ∧
    μ {p | p.1 ∈ data.A k 1 i ∧
    p.2 ∈ (I data) (data.T k 1) (data.j k 1 i)}ᶜ = 0 ∧
    ENNReal.ofReal (h / H) * data.ν k (data.γ k 1 i) (data.A k 1 i) ≤ μ Set.univ ∧
    z₀ 0 = (((data.j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ data.T k 1) ∧
    (∀ e, |z₀ e| ≤ H) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ (I data) (data.T k 1) (data.j k 1 i), ∀ e : Fin 2, |(![t, (y data) p.1 t] e - z₀ e) / h| ≤ H) ∧
    (∀ q : Fin 2 → ℤ, μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q} ≤ ENNReal.ofReal ((H * h) * data.N k ^ (-2 * Z)) * data.ν k (data.γ k 1 i) (data.A k 1 i)) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∀ c : ℤ, data.π k (data.γ k 1 i) ((vel data) k r c) ≤ ENNReal.ofReal (H * data.N k ^ (-data.S * r))) ∧
    ∀ (q : Fin 3 → ℤ) (c : ℤ), μ {p | (phys data) k B p = q ∧
    p.1.2 1 ∈ (vel data) k r c} ≤ ENNReal.ofReal (H) * μ {p | (phys data) k B p = q} * data.π k (data.γ k 1 i) ((vel data) k r c)) ∧
    (∀ e, (𝒯 e).totalDegree ≤ D ∧
    ∀ b, |(𝒯 e).coeff b| ≤ H) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ (I data) (data.T k 1) (data.j k 1 i), |p.1.2 3 + 2 * t * p.1.2 4 - ∑ e : Fin 2, MvPolynomial.eval (fun e : Fin 2 => ((![t,(y data) p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) (𝒯 e) * (![1,p.1.2 1] : Fin 2 → ℝ) e| ≤ H * data.N k ^ (-1 : ℝ) * h ^ (-(3 : ℝ)/4)) ∧
    (∀ w : ℝ, data.N k ^ (-1 : ℝ) * h ^ ((1 : ℝ)/8) ≤ w → w ≤ data.N k ^ (-1 : ℝ) → Set.Finite {q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q.1 ∧
    (⌊(x data) p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0} ∧
    ({q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q.1 ∧
    (⌊(x data) p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0}.ncard : ℝ) ≤ H * data.N k ^ (2 * Z) * (data.N k ^ (-1 : ℝ) / w) ^ data.d)

/-- The named pointwise output unfolds to the frozen conclusion without a change of type. -/
theorem fieldStatement_of_packet_conclusions (data : Data) (H : ℕ → ℝ) (D : ℕ) (Z B : ℝ)
    (hH : subpower data H) (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B)
    (hcon : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∃ (i : Fin (data.n k 1))
      (μ : Measure Incidence) (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ),
      PacketConclusion data k i μ z₀ 𝒯 (H k) D Z B R) : fieldStatement data := by
  exact ⟨H, D, Z, B, hH, hZ, hB, hcon⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
