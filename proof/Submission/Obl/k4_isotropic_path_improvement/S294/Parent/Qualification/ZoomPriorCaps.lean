-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomPriorCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomPriorCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomPriorCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomPriorCaps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

private theorem divided_mem_Ico (ρ : ℝ) (hρ : 0 < ρ) (x z a q : ℝ) :
    (x - z) / ρ ∈ Ico a (a + q) ↔
      x ∈ Ico (z + ρ * a) (z + ρ * a + ρ * q) := by
  rw [mem_Ico, mem_Ico, le_div_iff₀ hρ, div_lt_iff₀ hρ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The zoomed cube is an actual translated spatial cube in the old
coordinates, at the SAME time and of side `rho*q`. -/
theorem inCube_zoom_iff (ρ : ℝ) (hρ : 0 < ρ) (center c : Fin 7 → ℝ)
    (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ) :
    InCube (zoomCoefficients ρ center c) t a b q ↔
      InCube c t (zx center t + ρ * a)
        (fun i => zy center t i + ρ * b i) (ρ * q) := by
  simp only [InCube, zx_zoom, zy_zoom]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨(divided_mem_Ico ρ hρ _ _ _ _).mp hx,
      fun i => (divided_mem_Ico ρ hρ _ _ _ _).mp (hy i)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(divided_mem_Ico ρ hρ _ _ _ _).mpr hx,
      fun i => (divided_mem_Ico ρ hρ _ _ _ _).mpr (hy i)⟩

/-- The original numerator and original parameter floor have the SAME
palette factor. Their ratio is the desired spatial scale ratio. -/
theorem original_zoom_mass_ratio (ρ r q K s : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) (hq : 0 < q) (hK : 0 < K)
    (num bin palette : ENNReal)
    (hcap : num ≤ ENNReal.ofReal (K * (ρ * q) ^ s) * palette)
    (hfloor : ENNReal.ofReal ((ρ * r) ^ s / K) * palette ≤ bin) :
    num ≤ ENNReal.ofReal (K ^ 2 * (q / r) ^ s) * bin := by
  have hscale : K ^ 2 * (q / r) ^ s * ((ρ * r) ^ s / K) = K * (ρ * q) ^ s := by
    rw [Real.div_rpow hq.le hr.le, Real.mul_rpow hρ.le hr.le,
      Real.mul_rpow hρ.le hq.le]
    field_simp [hK.ne', (Real.rpow_pos_of_pos hr s).ne']
  have hscale' : ENNReal.ofReal (K * (ρ * q) ^ s) =
      ENNReal.ofReal (K ^ 2 * (q / r) ^ s) * ENNReal.ofReal ((ρ * r) ^ s / K) := by
    rw [← ENNReal.ofReal_mul (by positivity), hscale]
  calc
    num ≤ ENNReal.ofReal (K * (ρ * q) ^ s) * palette := hcap
    _ = ENNReal.ofReal (K ^ 2 * (q / r) ^ s) *
        (ENNReal.ofReal ((ρ * r) ^ s / K) * palette) := by rw [hscale', mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl hfloor

/-- The original conditional spatial cap after a real parameter zoom.
Both the numerator and the bin denominator still use the FULL original
prior; restricting incidence labels never changes the latter. -/
theorem original_zoom_conditional_cap {Λ J : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (A : Set Λ) (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (bin : Λ → J) (j : J)
    (ρ r q K s : ℝ) (hρ : 0 < ρ) (hr : 0 < r) (hq : 0 < q) (hK : 0 < K)
    (center : Fin 7 → ℝ) (t a : ℝ) (b : Fin 2 → ℝ)
    (palette : ENNReal) (hbinA : {l | bin l = j} ⊆ A)
    (hcap : ν {l | bin l = j ∧ (l, t) ∈ E ∧
      InCube (c l) t (zx center t + ρ * a)
        (fun i => zy center t i + ρ * b i) (ρ * q)} ≤
      ENNReal.ofReal (K * (ρ * q) ^ s) * palette)
    (hfloor : ENNReal.ofReal ((ρ * r) ^ s / K) * palette ≤ ν {l | bin l = j}) :
    ((ν A)⁻¹ • ν.restrict A)
      {l | bin l = j ∧ (l, t) ∈ E ∧ InCube (zoomCoefficients ρ center (c l)) t a b q} ≤
      ENNReal.ofReal (K ^ 2 * (q / r) ^ s) *
        ((ν A)⁻¹ • ν.restrict A) {l | bin l = j} := by
  let B : Set Λ := {l | bin l = j}
  let H : Set Λ :=
    {l | bin l = j ∧ (l, t) ∈ E ∧ InCube (zoomCoefficients ρ center (c l)) t a b q}
  have hHA : H ⊆ A := fun _ hl => hbinA hl.1
  have hnum : ν H ≤ ENNReal.ofReal (K * (ρ * q) ^ s) * palette := by
    simpa only [H, inCube_zoom_iff ρ hρ] using hcap
  have h := original_zoom_mass_ratio ρ r q K s hρ hr hq hK (ν H) (ν B) palette hnum hfloor
  change ((ν A)⁻¹ • ν.restrict A) H ≤ _ * ((ν A)⁻¹ • ν.restrict A) B
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_eq_self ν hHA,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_eq_self ν hbinA]
  exact (mul_le_mul' le_rfl h).trans_eq (by ring)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
