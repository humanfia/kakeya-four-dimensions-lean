import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonFrame
import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonMeshNumerics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonBuild.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace ProjectedComparisonFrame

/-- Construct every comparison mesh at one fixed power from coarse
power bounds on the actual geometry and projected coefficients. -/
def of_power_bounds {α : Type} [MeasurableSpace α] {p : Parent α}
    {k : ℕ} {sc sf m H h g b C : ℝ} {σ : Measure (α × ℝ)}
    {A₀ A₁ : ProjectedLayer α}
    (hp : p.Valid) (hC : 1 ≤ C) (hsc : 0 ≤ sc) (hsf : sc ≤ sf) (hsfC : sf ≤ C)
    (hm : 0 ≤ m) (hmC : m ≤ C) (hH : 1 ≤ H) (hKH : p.K k ≤ H) (hHX : H ≤ p.N k ^ C)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g ≤ b)
    (hhlo : p.N k ^ (-C) ≤ h) (hhhi : h ≤ p.N k ^ C) (hgX : g ≤ p.N k ^ C)
    (hblo : p.N k ^ (-C) ≤ b) (hbhi : b ≤ p.N k ^ C)
    (a₀ : A₀.SourceAtlas p k sc m H h g b σ) (a₁ : A₁.SourceAtlas p k sf m H h g b σ)
    (hσ : σ ≤ p.μ k)
    (hc₀ : ∀ i e, |(A₀.G i).coeff e| ≤ p.N k ^ C)
    (hc₁ : ∀ i e, |(A₁.G i).coeff e| ≤ p.N k ^ C)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ sf → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) (80 * C) ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * (80 * C) - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁}) :
    ProjectedComparisonFrame p k sc sf m H h g b σ := by
  let X := p.N k ^ C
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hX : 2 ≤ X := by
    calc
      _ ≤ p.N k := hp.scale k
      _ = p.N k ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hC
  have hrecip : X ^ (-1 : ℝ) = p.N k ^ (-C) := by
    dsimp [X]
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  have haf : X ^ (-1 : ℝ) ≤ p.N k ^ (-sf) := by
    rw [hrecip]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hsfC)
  have hχlo : X ^ (-1 : ℝ) ≤ p.N k ^ (-m) := by
    rw [hrecip]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hmC)
  have hχhi : p.N k ^ (-m) ≤ X :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hw := comparison_mesh_from_power_bound hX (zero_le_one.trans (hp.subpower.1 k))
    (hKH.trans hHX) hH (by simpa only [hrecip] using hhlo) hhhi hgX
    (by simpa only [hrecip] using hblo) hbhi haf hχlo hχhi
  have hmesh : p.N k ^ (-(80 * C)) = X ^ (-80 : ℝ) := by
    dsimp [X]
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  exact {
    coarse := A₀
    fine := A₁
    coarseAtlas := a₀
    fineAtlas := a₁
    le_mu := hσ
    coarse_nonneg := hsc
    coarse_le_fine := hsf
    loss_one := hH
    time_pos := hh
    slope_pos := hg
    width_pos := hb
    domain_motion := hmove
    δ := X ^ (-40 : ℝ)
    η := X ^ (-20 : ℝ)
    B := X
    V := 3 * X
    r := 80 * C
    mesh_pos := hw.mesh_pos
    mesh_small := hw.mesh_small
    physical_nonneg := hw.physical_nonneg
    physical_small := hw.physical_small
    coeff_nonneg := hw.coeff_nonneg
    velocity_nonneg := hw.velocity_nonneg
    cap_mesh_nonneg := by linarith
    domain_velocity := hw.domain_velocity
    major_velocity := hw.major_velocity
    coarse_coeff := hc₀
    fine_coeff := hc₁
    cap_resolution := by simpa only [hmesh] using hw.cap_resolution
    cap_time := by simpa only [hmesh] using hw.cap_time
    cap_major_width := by simpa only [hmesh] using hw.cap_major_width
    cap_transverse_width := by simpa only [hmesh] using hw.cap_transverse_width
    cap_major_motion := by simpa only [hmesh] using hw.cap_major_motion
    cap_transverse_motion := by simpa only [hmesh] using hw.cap_transverse_motion
    jitter_time := hw.jitter_time
    jitter_transverse := hw.jitter_transverse
    jitter_resolution := hw.jitter_resolution
    native_caps := hcap }

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
