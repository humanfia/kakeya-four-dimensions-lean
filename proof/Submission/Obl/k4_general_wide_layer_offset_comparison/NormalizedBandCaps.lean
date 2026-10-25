import Submission.Obl.k4_general_wide_layer_offset_comparison.NormalizedSourceCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/NormalizedBandCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- A normalized source cell has its expected area ceiling for any native
band thickness above the resolved minimum, in original palette units. -/
theorem normalized_band_cell_cap (hbase : p.Basic)
    {k : ℕ} {r smax m δ q b L Δ : ℝ}
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d)
    (hsmax : 0 ≤ smax) (hΔ : 0 < Δ) (hmin : p.N k ^ (-smax) ≤ Δ)
    (hδ : 0 < δ)
    (hq : 0 < q) (hb : 0 < b) (hL : 0 ≤ L)
    (hdtime : p.N k ^ (-r) ≤ q * δ)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hdb : p.N k ^ (-r) ≤ b * δ)
    (hmχ : L * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hmb : L * p.N k ^ (-r) ≤ b * δ)
    (time u v : ℝ) (z₀ v₀ : ℤ)
    (hv₀ : |(v₀ : ℝ) * p.N k ^ (-m)| ≤ L) (hv : |v| ≤ L)
    (G : MvPolynomial (Fin 2) ℝ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (key : Fin 2 → ℤ)
    (hdata : ∀ ω ∈ E, ω.2 ∈ Icc (0 : ℝ) 1 ∧
      ⌊p.b k ω.1 0 / (p.N k ^ (-m))⌋ = z₀ ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀ ∧
      meshCode2 δ (projectedDomainCoordinates time q u v b
        ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2]) = key)
    (hfit : ∀ ω ∈ E,
      |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2] G| ≤ Δ)
    (hvariation : ∀ ω ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-r)) →
      |eval ![ω.2, (p.x k ω.1 ω.2) 2] G - eval ![y 0, y 2] G| ≤ p.N k ^ (-smax))
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ smax → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁}) :
    σ E ≤ (ENNReal.ofReal (8400 * p.K k ^ 2 * p.N k ^ (-m) * q * b * Δ ^ p.d) *
      p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀}) * ENNReal.ofReal (δ ^ 2) := by
  have hNp : 0 < p.N k := by linarith
  let center : Fin 2 → ℝ := ![(z₀ : ℝ) * p.N k ^ (-m), u + b * ((key 1 : ℝ) * δ)]
  let velocity : Fin 2 → ℝ := ![(v₀ : ℝ) * p.N k ^ (-m), v]
  let width : Fin 2 → ℝ := ![2 * p.N k ^ (-m), b * δ]
  have hbox (ω : α × ℝ) (hω : ω ∈ E) :
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox
          (time + q * ((key 0 : ℝ) * δ)) (q * δ) center velocity width := by
    obtain ⟨ht, hz, hvbin, hcell⟩ := hdata ω hω
    have hct : ⌊((ω.2 - time) / q) / δ⌋ = key 0 := congrFun hcell 0
    have hcy : ⌊(((p.x k ω.1 ω.2) 2 - (u + ω.2 * v)) / b) / δ⌋ = key 1 := by
      convert congrFun hcell 1 using 1 <;> dsimp [meshCode2, projectedDomainCoordinates] <;> congr 3 <;> ring
    refine ⟨normalized_bin_bound hq hδ hct, ?_⟩
    intro i
    fin_cases i
    · have h := intercept_velocity_bin_tube (Real.rpow_pos_of_pos hNp _) hz hvbin ht
      simpa [center, velocity, width,
        Submission.Obl.k4_critical_intercept_concentration.Data.x] using h
    · have h := normalized_bin_bound hb hδ hcy
      convert h using 1 <;> dsimp [center, velocity, width] <;> congr 1 <;> ring
  have hc := native_band_box_cap p hbase hN hK hd hsmax hΔ hmin hdtime hL
    (time + q * ((key 0 : ℝ) * δ)) center velocity width
    (by intro i; fin_cases i; exact hv₀; exact hv)
    (by intro i; fin_cases i; exact hdχ; exact hdb)
    (by intro i; fin_cases i; exact hmχ; exact hmb)
    v₀ (fun x => eval ![x 0, x 2] G) σ hσ E hbox
    (fun ω hω => (hdata ω hω).2.2.1)
    (by simpa using hfit) (by simpa using hvariation) hcap
  have heq : 4200 * p.K k ^ 2 * Δ ^ p.d * (q * δ) * width 0 * width 1 =
      (8400 * p.K k ^ 2 * p.N k ^ (-m) * q * b * Δ ^ p.d) * δ ^ 2 := by
    dsimp [width]
    ring
  rw [heq, ENNReal.ofReal_mul (by positivity)] at hc
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hc


end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
