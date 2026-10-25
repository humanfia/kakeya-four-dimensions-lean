import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeSourceCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.RawMeshCoupling
import Submission.Lib.K4ProjectedGroups.GroupCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/NormalizedSourceCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

def projectedDomainCoordinates (time q u v b : ℝ) (z : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(z 0 - time) / q, (z 2 - u - z 0 * v) / b]

theorem normalized_bin_bound {x center scale δ : ℝ} {j : ℤ}
    (hscale : 0 < scale) (hδ : 0 < δ)
    (hcode : ⌊((x - center) / scale) / δ⌋ = j) :
    |x - (center + scale * ((j : ℝ) * δ))| ≤ scale * δ := by
  obtain ⟨hlo, hhi⟩ := Submission.Lib.K4ProjectedGroups.floor_bounds hδ hcode
  have hlo' := (le_div_iff₀ hscale).mp hlo
  have hhi' := (div_le_iff₀ hscale).mp hhi
  rw [abs_le]
  constructor <;> nlinarith

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The original native cap on one cell in normalized common-domain
coordinates, with its exact `time-length * transverse-width * chi` reference
Jacobian and unchanged original palette. -/
theorem normalized_source_cell_cap
    {k : ℕ} {r s m δ q b L : ℝ}
    (hN : 0 < p.N k) (hK : 0 ≤ p.K k) (hδ : 0 < δ)
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
      |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2] G| ≤ p.N k ^ (-s))
    (hvariation : ∀ ω ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-r)) →
      |eval ![ω.2, (p.x k ω.1 ω.2) 2] G - eval ![y 0, y 2] G| ≤ p.N k ^ (-s))
    (hcap : ∀ (c : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀}) :
    σ E ≤ (ENNReal.ofReal (8400 * p.K k * p.N k ^ (-m) * q * b * p.N k ^ (-p.d * s)) *
      p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀}) * ENNReal.ofReal (δ ^ 2) := by
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
    · have h := intercept_velocity_bin_tube (Real.rpow_pos_of_pos hN _) hz hvbin ht
      simpa [center, velocity, width,
        Submission.Obl.k4_critical_intercept_concentration.Data.x] using h
    · have h := normalized_bin_bound hb hδ hcy
      convert h using 1 <;> dsimp [center, velocity, width] <;> congr 1 <;> ring
  have hc := native_source_box_cap p hN hK hdtime hL
    (time + q * ((key 0 : ℝ) * δ)) center velocity width
    (by intro i; fin_cases i; exact hv₀; exact hv)
    (by intro i; fin_cases i; exact hdχ; exact hdb)
    (by intro i; fin_cases i; exact hmχ; exact hmb)
    v₀ (fun x => eval ![x 0, x 2] G) σ hσ E hbox
    (fun ω hω => (hdata ω hω).2.2.1)
    (by simpa using hfit) (by simpa using hvariation) hcap
  have heq : 4200 * p.K k * p.N k ^ (-p.d * s) * (q * δ) * width 0 * width 1 =
      (8400 * p.K k * p.N k ^ (-m) * q * b * p.N k ^ (-p.d * s)) * δ ^ 2 := by
    dsimp [width]
    ring
  rw [heq, ENNReal.ofReal_mul (by positivity)] at hc
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hc

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
