import Submission.Obl.k4_scalar_grid_cartesian_field.RectangularCaps

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- Exact velocity confinement on a part where the transverse derivative is large. -/
theorem velocity_interval_of_large_derivative {A B V D Q γ : ℝ}
    (hQ : 0 < Q) (hγ : 0 ≤ γ) (hB : Q ≤ |B|)
    (hdir : |A + V * B| ≤ D) (hD : D ≤ Q * γ) :
    |V - (-A / B)| ≤ γ := by
  have hBpos : 0 < |B| := lt_of_lt_of_le hQ hB
  have hBne : B ≠ 0 := abs_pos.mp hBpos
  calc
    _ = |(A + V * B) / B| := by congr 1; field_simp; ring
    _ = |A + V * B| / |B| := abs_div _ _
    _ ≤ (Q * γ) / |B| := div_le_div_of_nonneg_right (hdir.trans hD) hBpos.le
    _ ≤ (|B| * γ) / |B| := by gcongr
    _ = γ := mul_div_cancel_left₀ γ hBpos.ne'

/-- The original joint palette bound is exactly a cap on four scalar floor codes. -/
theorem rectangular_cap_fin_four {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x V : Ω → ℝ)
    (α δ γ : ℝ) (B : ENNReal)
    (hcap : ∀ (q : Fin 2 → ℤ) (c a : ℤ),
      ρ {p | (fun e => (⌊z p e / α⌋ : ℤ)) = q ∧
        (⌊x p / δ⌋ : ℤ) = c ∧ (⌊V p / γ⌋ : ℤ) = a} ≤ B) :
    ∀ q : Fin 4 → ℤ,
      ρ {p | (fun e : Fin 4 => (⌊(![z p 0, z p 1, x p, V p] : Fin 4 → ℝ) e /
        (![α, α, δ, γ] : Fin 4 → ℝ) e⌋ : ℤ)) = q} ≤ B := by
  intro q
  apply (measure_mono (t := {p | (fun e => (⌊z p e / α⌋ : ℤ)) = ![q 0, q 1] ∧
    (⌊x p / δ⌋ : ℤ) = q 2 ∧ (⌊V p / γ⌋ : ℤ) = q 3}) ?_).trans (hcap _ _ _)
  intro p hp
  refine ⟨?_, ?_, ?_⟩
  · funext e
    fin_cases e
    · simpa using congrFun hp 0
    · simpa using congrFun hp 1
  · simpa using congrFun hp 2
  · simpa using congrFun hp 3

/-- On a steep portion of a packet, one normalized base cell has small original mass.
Only the original spatial and original-prior velocity caps are used. -/
theorem normalized_steep_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x V : Ω → ℝ)
    (f g₀ g₁ : (Fin 2 → ℝ) → ℝ) (S : Set Ω)
    {h ξ α δ γ K D ε Q : ℝ} (hh : 0 < h) (hξ : 0 < ξ)
    (hα : 0 < α) (hδ : 0 < δ) (hγ : 0 < γ) (hK : 0 ≤ K)
    (_hε : 0 ≤ ε) (hQ : 0 < Q) (origin : Fin 2 → ℝ) (C : ℕ)
    (hwidth : h * ξ ≤ (C : ℝ) * α) (hKC : 2 * K + 1 ≤ C) (hC : 1 ≤ C)
    (hsmall : D + (1 + K) * ε ≤ Q * γ) (B : ENNReal)
    (hcap : ∀ (q : Fin 2 → ℤ) (c a : ℤ),
      ρ {p | (fun e => (⌊z p e / α⌋ : ℤ)) = q ∧
        (⌊x p / δ⌋ : ℤ) = c ∧ (⌊V p / γ⌋ : ℤ) = a} ≤ B)
    (hfit : ∀ p ∈ S, |x p - f (z p)| ≤ K * δ)
    (hvel : ∀ p ∈ S, |V p| ≤ K)
    (hdir : ∀ p ∈ S, |g₀ (z p) + V p * g₁ (z p)| ≤ D)
    (hsteep : ∀ p ∈ S, Q ≤ |g₁ (z p)|)
    (hvar : ∀ p ∈ S, ∀ p' ∈ S,
      (fun e => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)) =
        (fun e => (⌊(z p' e - origin e) / h / ξ⌋ : ℤ)) →
      |f (z p) - f (z p')| ≤ δ ∧
      |g₀ (z p) - g₀ (z p')| ≤ ε ∧ |g₁ (z p) - g₁ (z p')| ≤ ε) :
    ∀ q : Fin 2 → ℤ,
      ρ ({p | (fun e => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)) = q} ∩ S) ≤
        ((2 * C + 1) ^ 4 : ℕ) * B := by
  intro q
  let U := {p | (fun e => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)) = q} ∩ S
  rcases U.eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [show {p | (fun e => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)) = q} ∩ S = ∅ from he,
      measure_empty]
    exact bot_le
  apply mass_le_of_rectangular_closeness ρ
    (fun p => ![z p 0, z p 1, x p, V p]) ![α, α, δ, γ]
    (by intro e; fin_cases e <;> simp [hα, hδ, hγ])
    U ![z p₀ 0, z p₀ 1, x p₀, -g₀ (z p₀) / g₁ (z p₀)] C B ?_
    (rectangular_cap_fin_four ρ z x V α δ γ B hcap)
  intro p hp e
  have hcell := hp.1.trans hp₀.1.symm
  have hbase := normalized_cell_diameter hh hξ hcell
  obtain ⟨hf, hg₀, hg₁⟩ := hvar p hp.2 p₀ hp₀.2 hcell
  have hdir₀ : |g₀ (z p₀) + V p * g₁ (z p₀)| ≤ D + (1 + K) * ε := by
    calc
      _ = |(g₀ (z p) + V p * g₁ (z p)) + (g₀ (z p₀) - g₀ (z p)) +
        V p * (g₁ (z p₀) - g₁ (z p))| := by congr 1; ring
      _ ≤ |g₀ (z p) + V p * g₁ (z p)| + |g₀ (z p₀) - g₀ (z p)| +
          |V p * (g₁ (z p₀) - g₁ (z p))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ D + ε + K * ε := by
        rw [abs_mul, abs_sub_comm (g₀ (z p₀)), abs_sub_comm (g₁ (z p₀))]
        exact add_le_add (add_le_add (hdir p hp.2) hg₀)
          (mul_le_mul (hvel p hp.2) hg₁ (abs_nonneg _) hK)
      _ = _ := by ring
  fin_cases e
  · exact (hbase 0).trans hwidth
  · exact (hbase 1).trans hwidth
  · change |x p - x p₀| ≤ (C : ℝ) * δ
    calc
      _ = |(x p - f (z p)) + (f (z p) - f (z p₀)) + (f (z p₀) - x p₀)| := by ring_nf
      _ ≤ |x p - f (z p)| + |f (z p) - f (z p₀)| + |f (z p₀) - x p₀| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * δ + δ + K * δ := by
        rw [abs_sub_comm (f (z p₀))]
        exact add_le_add (add_le_add (hfit p hp.2) hf) (hfit p₀ hp₀.2)
      _ ≤ _ := by nlinarith
  · change |V p - (-g₀ (z p₀) / g₁ (z p₀))| ≤ (C : ℝ) * γ
    exact (velocity_interval_of_large_derivative hQ hγ.le (hsteep p₀ hp₀.2)
      hdir₀ hsmall).trans (le_mul_of_one_le_left hγ.le (by exact_mod_cast hC))

end Submission.Obl.k4_scalar_grid_cartesian_field
