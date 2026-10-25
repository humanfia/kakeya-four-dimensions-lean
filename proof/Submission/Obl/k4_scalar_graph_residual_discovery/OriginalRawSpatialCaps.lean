/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalRawSpatialCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalParameterCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.VelocityBins

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace ScalarData

/-- Raw fixed-time spatial caps and the two-sided ORIGINAL coefficient
prior bounds, directly from the canonical preparation certificate. These
are available on every later subset without modifying the original palette. -/
theorem prepData.original_raw_spatial_caps {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop, ∀ (g : Fin (D.W k)) (u v : ℝ),
      T⁻¹ ≤ u → u ≤ T → T⁻¹ ≤ v → v ≤ T →
      (∃ m : ℕ, u = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      (∃ m : ℕ, v = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      (∀ b : Fin 5 → ℤ,
        (D.ρ k g).restrict (E₀ k g) {p | cell (D.N k ^ (-u)) p.1.2 = b} ≠ 0 →
          ENNReal.ofReal ((D.N k ^ (-u)) ^ (1 + D.d) / H k) *
              D.π k g (scalarVelocityBin (D.N k ^ (-u)) (b 1)) ≤
            θ k g {l | cell (D.N k ^ (-u)) l.2 = b} ∧
          θ k g {l | cell (D.N k ^ (-u)) l.2 = b} ≤
            ENNReal.ofReal (H k * (D.N k ^ (-u)) ^ (1 + D.d)) *
              D.π k g (scalarVelocityBin (D.N k ^ (-u)) (b 1))) ∧
      ∀ (E : Set ScalarIncidence), E ⊆ E₀ k g → ∀ (t : ℝ) (b : Fin 5 → ℤ) (z : Fin 2 → ℤ),
        θ k g {l | (l, t) ∈ E ∧ cell (D.N k ^ (-u)) l.2 = b ∧
          cell (D.N k ^ (-v)) (Zoom.spatial l t) = z} ≤
            ENNReal.ofReal (H k * (D.N k ^ (-v)) ^ (1 + D.d)) *
              D.π k g (scalarVelocityBin (D.N k ^ (-u)) (b 1)) := by
  have hdata := (Classical.choose_spec hprep.2).2
  intro T hT
  filter_upwards [hdata T hT] with k hk
  intro g u v hulo huhi hvlo hvhi humesh hvmesh
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hpow (w : ℝ) : D.N k ^ (-w - D.d * w) = (D.N k ^ (-w)) ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hpow' : D.N k ^ (-(1 + D.d) * u) = (D.N k ^ (-u)) ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hcoeff (l : ScalarLine) : D.coeff k u l = cell (D.N k ^ (-u)) l.2 := by
    funext e
    rfl
  have hvel (j : ℤ) : D.vel k u j = scalarVelocityBin (D.N k ^ (-u)) j := rfl
  obtain ⟨_, _, _, _, _, _, _, hgrid, hfixed⟩ := hk.2 g
  refine ⟨?_, ?_⟩
  · intro b hactive
    have hactive' : (D.ρ k g).restrict (E₀ k g) {p | D.coeff k u p.1 = b} ≠ 0 := by
      simpa only [hcoeff] using hactive
    have hh := (hgrid u hulo huhi humesh).2.2.2.1 b hactive'
    simpa only [hcoeff, hvel, hpow'] using hh
  · intro E hE t b z
    obtain ⟨i, hi⟩ := humesh
    obtain ⟨j, hj⟩ := hvmesh
    have hh := hfixed v v u t hvlo hvhi hvlo hvhi hulo huhi ⟨j, j, i, hj, hj, hi⟩
      (z 0) (z 1) (b 1)
    rw [hpow, hvel] at hh
    apply (measure_mono ?_).trans hh
    intro l hl
    exact ⟨hE hl.1, congrFun hl.2.2 0, congrFun hl.2.2 1, congrFun hl.2.1 1⟩

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
