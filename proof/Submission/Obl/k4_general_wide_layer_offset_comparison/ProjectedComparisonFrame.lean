import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedMatchingLaw
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedBandCeiling

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonFrame.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

/-- Finite raw inputs to projected comparison. All ceilings are primitive
original native caps; the remaining fields are explicit mesh inequalities. -/
structure ProjectedComparisonFrame {α : Type} [MeasurableSpace α]
    (p : Parent α) (k : ℕ) (sc sf m H h g b : ℝ) (σ : Measure (α × ℝ)) where
  coarse : ProjectedLayer α
  fine : ProjectedLayer α
  coarseAtlas : coarse.SourceAtlas p k sc m H h g b σ
  fineAtlas : fine.SourceAtlas p k sf m H h g b σ
  le_mu : σ ≤ p.μ k
  coarse_nonneg : 0 ≤ sc
  coarse_le_fine : sc ≤ sf
  loss_one : 1 ≤ H
  time_pos : 0 < h
  slope_pos : 0 < g
  width_pos : 0 < b
  domain_motion : h * g ≤ b
  δ : ℝ
  η : ℝ
  B : ℝ
  V : ℝ
  r : ℝ
  mesh_pos : 0 < δ
  mesh_small : δ ≤ 1 / 32
  physical_nonneg : 0 ≤ η
  physical_small : η ≤ 1
  coeff_nonneg : 0 ≤ B
  velocity_nonneg : 0 ≤ V
  cap_mesh_nonneg : 0 ≤ r
  domain_velocity : p.K k + g ≤ V
  major_velocity : p.K k + p.N k ^ (-m) ≤ V
  coarse_coeff : ∀ i e, |(coarse.G i).coeff e| ≤ B
  fine_coeff : ∀ i e, |(fine.G i).coeff e| ≤ B
  cap_resolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-sf)
  cap_time : p.N k ^ (-r) ≤ (32 * h) * δ
  cap_major_width : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m)
  cap_transverse_width : p.N k ^ (-r) ≤ (32 * b) * δ
  cap_major_motion : V * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m)
  cap_transverse_motion : V * p.N k ^ (-r) ≤ (32 * b) * δ
  jitter_time : (32 * h) * δ ≤ η
  jitter_transverse : (V * (32 * h) + 32 * b) * δ ≤ η
  jitter_resolution : 54 * B * (p.K k + 1) ^ 4 * η ≤ H * p.N k ^ (-sf)
  native_caps : ∀ s : ℝ, 0 ≤ s → s ≤ sf → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
    p.μ k {ω | p.z k (p.N k) r ω = c ∧
      ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
      ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
    ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
      p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁}

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

include f

theorem finite_source (hp : p.Valid) : IsFiniteMeasure σ :=
  ⟨(f.le_mu univ).trans_lt ((Parent.Basic.mass_le p hp.basic k).trans_lt ENNReal.ofReal_lt_top)⟩

theorem fine_nonneg : 0 ≤ sf := f.coarse_nonneg.trans f.coarse_le_fine

theorem query_transverse (hp : p.Valid) {A : ProjectedLayer α} {s : ℝ}
    (q : A.SourceAtlas p k s m H h g b σ)
    (e : A.ActiveSlice p k h g b q.domains σ) :
    (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * f.δ ≤ f.η := by
  have ha := A.activeSlice_anchor_bounds p q.valid
    (show 0 < p.N k by linarith [hp.scale k]) f.time_pos f.slope_pos f.width_pos σ e
  have hv : |domainVelocity g e.val.2.val| * (32 * h) ≤ f.V * (32 * h) :=
    mul_le_mul_of_nonneg_right (ha.2.2.1.trans f.domain_velocity)
      (by have hh := f.time_pos; positivity)
  exact (mul_le_mul_of_nonneg_right (add_le_add hv (le_rfl : 32 * b ≤ 32 * b)) f.mesh_pos.le).trans
    f.jitter_transverse

/-- Every actual source color has its continuous density ceiling after
common-base smoothing, directly from the primitive original caps. -/
theorem query_cells (hp : p.Valid) {A : ProjectedLayer α} {s : ℝ}
    (q : A.SourceAtlas p k s m H h g b σ) (hs : 0 ≤ s) (hsf : s ≤ sf)
    (hcoeff : ∀ i e, |(A.G i).coeff e| ≤ f.B) (Q : Finset (Fin 2 → ℤ)) :
    q.CellCeiling f.δ Q := by
  have hN : 1 < p.N k := by linarith [hp.scale k]
  have hres : 54 * f.B * (p.K k + 1) ^ 4 * p.N k ^ (-f.r) ≤ p.N k ^ (-s) :=
    f.cap_resolution.trans (Real.rpow_le_rpow_of_exponent_le hN.le (neg_le_neg hsf))
  intro e cell _
  exact A.activeSlice_cell_cap p hp.basic q.valid hN (hp.subpower.1 k) hp.dimension_nonneg hs
    f.loss_one f.cap_mesh_nonneg f.coeff_nonneg f.time_pos f.slope_pos f.width_pos f.mesh_pos
    f.velocity_nonneg f.domain_velocity f.major_velocity hcoeff hres f.cap_time
    f.cap_major_width f.cap_transverse_width f.cap_major_motion f.cap_transverse_motion
    q.domains σ f.le_mu e (fun t ht hts => f.native_caps t ht (hts.trans hsf)) cell

/-- The concrete frame constructs the full two-color matching setup. Its
only inputs beyond the actual source atlases are raw native caps and mesh
resolution inequalities. -/
def matching (hp : p.Valid) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q) :
    AEWeightComparison f.coarseAtlas.Index f.fineAtlas.Index (Option ComparisonCode)
      ((α × ℝ) × EuclideanSpace ℝ (Fin 3)) := by
  letI := f.finite_source hp
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have haf : p.N k ^ (-sf) ≤ p.N k ^ (-sc) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg f.coarse_le_fine)
  have hH : 0 ≤ H := zero_le_one.trans f.loss_one
  have hAf := mul_le_mul_of_nonneg_left haf hH
  have he₀ : H * p.N k ^ (-sc) + 54 * f.B * (p.K k + 1) ^ 4 * f.η ≤
      2 * H * p.N k ^ (-sc) := by linarith [f.jitter_resolution]
  have he₁ : H * p.N k ^ (-sf) + 54 * f.B * (p.K k + 1) ^ 4 * f.η ≤
      2 * H * p.N k ^ (-sc) := by linarith [f.jitter_resolution]
  exact projectedMatchingLaw f.coarseAtlas f.fineAtlas hp.basic hN (hp.subpower.1 k) f.loss_one
    f.time_pos f.slope_pos f.width_pos f.domain_motion f.mesh_pos
    (by linarith [f.mesh_small]) f.physical_nonneg f.physical_small f.coeff_nonneg
    f.coarse_coeff f.fine_coeff f.jitter_time
    (f.query_transverse hp f.coarseAtlas) (f.query_transverse hp f.fineAtlas)
    (by have hHp : 0 < H := zero_lt_one.trans_le f.loss_one; positivity)
    he₀ he₁ Q hcover
    (f.query_cells hp f.coarseAtlas f.coarse_nonneg f.coarse_le_fine f.coarse_coeff Q)
    (f.query_cells hp f.fineAtlas f.fine_nonneg le_rfl f.fine_coeff Q)

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
