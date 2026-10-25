import Submission.Obl.k4_general_wide_layer_offset_comparison.Model
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.ResidualCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialLipschitz

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/NativeSourceCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

/-- Resolving a bounded quadratic projected predictor requires only a finer
base mesh. Its absolute coefficient height is absent from the final cap. -/
theorem projected_predictor_variation
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {B R δ : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcoeff : ∀ e, |G.coeff e| ≤ B)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ R)
    (hxy : ∀ i, |x i - y i| ≤ δ) :
    |eval ![x 0, x 2] G - eval ![y 0, y 2] G| ≤
      54 * B * (R + 1) ^ 4 * δ := by
  let X : Fin 2 → ℝ := ![x 0, x 2]
  let Y : Fin 2 → ℝ := ![y 0, y 2]
  have hX (i : Fin 2) : |X i| ≤ R + 1 := by
    fin_cases i <;> dsimp [X] <;> linarith [hx 0, hx 2]
  have hY (i : Fin 2) : |Y i| ≤ R + 1 := by
    have hh (j : Fin 3) : |y j| ≤ R + 1 := by
      calc
        _ ≤ |x j - y j| + |x j| := by
          simpa only [sub_zero, abs_sub_comm] using abs_sub_le (y j) (x j) 0
        _ ≤ _ := by linarith [hxy j, hx j]
    fin_cases i <;> exact hh _
  have hd : dist X Y ≤ δ := by
    apply (dist_pi_le_iff hδ).mpr
    intro i
    fin_cases i
    · simpa [X, Y, Real.dist_eq] using hxy 0
    · simpa [X, Y, Real.dist_eq] using hxy 2
  have h := Submission.Obl.k4_scalar_grid_parameter_preparation.binary_polynomial_lipschitz
    G 2 hG hB (by linarith : 1 ≤ R + 1) hcoeff X Y hX hY
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul, show (2 : ℝ) + 1 = 3 by norm_num,
    show (3 : ℝ) ^ 3 = 27 by norm_num] at h
  exact h.trans (mul_le_mul_of_nonneg_left hd (by positivity))

/-- The two original bins specify the horizontal base line to accuracy
`2 * χ` for every time in the full unit interval. -/
theorem intercept_velocity_bin_tube {χ t z v : ℝ} (hχ : 0 < χ)
    {z₀ v₀ : ℤ} (hz : ⌊z / χ⌋ = z₀) (hv : ⌊v / χ⌋ = v₀)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |z + t * v - ((z₀ : ℝ) * χ + t * ((v₀ : ℝ) * χ))| ≤ 2 * χ := by
  have hbin (w : ℝ) (a : ℤ) (ha : ⌊w / χ⌋ = a) :
      |w - (a : ℝ) * χ| ≤ χ := by
    have hlo := (le_div_iff₀ hχ).mp (ha ▸ Int.floor_le (w / χ))
    have hhi := (div_lt_iff₀ hχ).mp (ha ▸ Int.lt_floor_add_one (w / χ))
    rw [abs_le]
    constructor <;> linarith
  have htz : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  calc
    _ = |(z - (z₀ : ℝ) * χ) + t * (v - (v₀ : ℝ) * χ)| := by congr 1; ring
    _ ≤ |z - (z₀ : ℝ) * χ| + |t * (v - (v₀ : ℝ) * χ)| := abs_add_le _ _
    _ ≤ χ + 1 * χ := by
      rw [abs_mul]
      exact add_le_add (hbin z z₀ hz) (mul_le_mul htz (hbin v v₀ hv) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Integrate the original native joint caps across a moving source box.
Any earlier or later restriction of the original law is allowed; the palette
factor is still the one from the original velocity bin. -/
theorem native_source_box_cap
    {k : ℕ} {r s v radius L : ℝ} (hN : 0 < p.N k) (hK : 0 ≤ p.K k)
    (hmesh : p.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L)
    (hdw : ∀ i, p.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * p.N k ^ (-r) ≤ width i)
    (v₀ : ℤ) (G : (Fin 3 → ℝ) → ℝ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (hbox : ∀ ω ∈ E,
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width)
    (hvel : ∀ ω ∈ E, ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀)
    (hfit : ∀ ω ∈ E,
      |eval (p.x k ω.1 ω.2) (p.P k) -
        G ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2]| ≤ p.N k ^ (-s))
    (hvariation : ∀ ω ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-r)) →
      |G ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] - G y| ≤ p.N k ^ (-s))
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀}) :
    σ E ≤ ENNReal.ofReal (4200 * p.K k * p.N k ^ (-p.d * s) *
      radius * width 0 * width 1) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
  have hp : p.N k ^ (-3 * r - p.d * s) =
      p.N k ^ (-p.d * s) * (p.N k ^ (-r)) ^ 3 := by
    rw [← Real.rpow_mul_natCast, ← Real.rpow_add hN]
    · congr 1
      ring
    · exact hN.le
  calc
    σ E ≤ p.μ k E := hσ E
    _ ≤ _ := by
      have hc := Submission.Obl.k4_wide_velocity_lists_scalar_preparation.measure_resolved_moving_slab
        (p.μ k) (fun ω => ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2])
        (fun ω => eval (p.x k ω.1 ω.2) (p.P k)) G
        (fun ω => ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀) E
        (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
        hmesh hL (mul_nonneg hK (Real.rpow_nonneg hN.le (-p.d * s)))
        time 0 center velocity width hv hdw hmove hbox hvel
        (by simpa only [sub_zero] using hfit) hvariation
        (p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀}) (by
          intro q j
          have hh := hcap q j
          rw [hp] at hh
          change p.μ k {ω | p.z k (p.N k) r ω = q ∧
            ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
            ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤ _
          simpa only [mul_assoc] using hh)
      simpa only [mul_assoc] using hc

/-- A literal time--transverse rectangle in a fixed intercept/velocity bin
has the expected source ceiling. In particular the fine intercept mesh is a
factor in the reference weight, rather than a count lost after restriction. -/
theorem native_source_rectangle_cap
    {k : ℕ} {r s v radius transverse L : ℝ}
    (hN : 0 < p.N k) (hK : 0 ≤ p.K k) (hL : 0 ≤ L)
    (hmesh : p.N k ^ (-r) ≤ radius)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-v))
    (hdw : p.N k ^ (-r) ≤ transverse)
    (hmχ : L * p.N k ^ (-r) ≤ 2 * p.N k ^ (-v))
    (hmw : L * p.N k ^ (-r) ≤ transverse)
    (time y₀ : ℝ) (z₀ v₀ : ℤ)
    (hv₀ : |(v₀ : ℝ) * p.N k ^ (-v)| ≤ L)
    (G : MvPolynomial (Fin 2) ℝ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (hdata : ∀ ω ∈ E, ω.2 ∈ Icc (0 : ℝ) 1 ∧ |ω.2 - time| ≤ radius ∧
      |(p.x k ω.1 ω.2) 2 - y₀| ≤ transverse ∧
      ⌊p.b k ω.1 0 / (p.N k ^ (-v))⌋ = z₀ ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀)
    (hfit : ∀ ω ∈ E,
      |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2] G| ≤ p.N k ^ (-s))
    (hvariation : ∀ ω ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-r)) →
      |eval ![ω.2, (p.x k ω.1 ω.2) 2] G - eval ![y 0, y 2] G| ≤ p.N k ^ (-s))
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀}) :
    σ E ≤ ENNReal.ofReal (8400 * p.K k * p.N k ^ (-v) *
      p.N k ^ (-p.d * s) * radius * transverse) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = v₀} := by
  let center : Fin 2 → ℝ := ![(z₀ : ℝ) * p.N k ^ (-v), y₀]
  let velocity : Fin 2 → ℝ := ![(v₀ : ℝ) * p.N k ^ (-v), 0]
  let width : Fin 2 → ℝ := ![2 * p.N k ^ (-v), transverse]
  have hbox (ω : α × ℝ) (hω : ω ∈ E) :
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width := by
    obtain ⟨ht, htime, hy, hz, hv⟩ := hdata ω hω
    refine ⟨htime, ?_⟩
    intro i
    fin_cases i
    · have h := intercept_velocity_bin_tube (Real.rpow_pos_of_pos hN _) hz hv ht
      simpa [center, velocity, width,
        Submission.Obl.k4_critical_intercept_concentration.Data.x] using h
    · simpa [center, velocity, width] using hy
  have hc := native_source_box_cap p hN hK hmesh hL time center velocity width
    (by intro i; fin_cases i; exact hv₀; simpa [velocity] using hL)
    (by intro i; fin_cases i; exact hdχ; exact hdw)
    (by intro i; fin_cases i; exact hmχ; exact hmw)
    v₀ (fun x => eval ![x 0, x 2] G) σ hσ E hbox
    (fun ω hω => (hdata ω hω).2.2.2.2)
    (by simpa using hfit) (by simpa using hvariation) hcap
  convert hc using 1 <;> dsimp [width] <;> congr 2 <;> ring

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
