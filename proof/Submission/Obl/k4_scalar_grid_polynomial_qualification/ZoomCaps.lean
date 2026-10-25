import Submission.Obl.k4_scalar_grid_polynomial_qualification.CoefficientZoom
import Submission.Obl.k4_scalar_grid_polynomial_qualification.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def spatial (l : ScalarLine) (t : ℝ) : Fin 2 → ℝ := ![scalarY l t, scalarX l t]

def zoomSpatial (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) : Fin 2 → ℝ :=
  ![y ρ q l t, x ρ q l t]

theorem zoomSpatial_eq (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) (e : Fin 2) :
    zoomSpatial ρ q l t e = (spatial l t e - spatial (center ρ q) t e) / ρ := by
  fin_cases e
  · exact y_eq ρ q l t
  · exact x_eq ρ q l t

theorem subtract_div_mem_Ico {ρ z c a r : ℝ} (hρ : 0 < ρ)
    (hz : (z - c) / ρ ∈ Ico a (a + r)) :
    z ∈ Ico (c + ρ * a) (c + ρ * a + ρ * r) := by
  have hlo := (le_div_iff₀ hρ).1 hz.1
  have hhi := (div_lt_iff₀ hρ).1 hz.2
  constructor <;> nlinarith only [hlo, hhi]

/-- The fixed-time cap on the original grid gives the required cap for the
zoomed spatial cube. The palette reference stays in the original units. -/
theorem zoom_cube_cap {θ : Measure ScalarLine} (E : Set ScalarIncidence)
    (t : ℝ) {ρ δ r : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hr : 0 ≤ r)
    (q : Fin 5 → ℤ) (C : ENNReal)
    (hcap : ∀ z, θ {l | (l, t) ∈ E ∧ cell δ (spatial l t) = z} ≤ C)
    (a : Fin 2 → ℝ) :
    θ {l | (l, t) ∈ E ∧ ∀ e, zoomSpatial ρ q l t e ∈ Ico (a e) (a e + r)} ≤
      ENNReal.ofReal ((ρ * r / δ + 2) ^ 2) * C := by
  have h := cube_cap_of_cell_caps θ {l | (l, t) ∈ E} (fun l => spatial l t)
    hδ (mul_nonneg hρ.le hr) C hcap (fun e => spatial (center ρ q) t e + ρ * a e)
  apply le_trans (measure_mono (t := {l | (l, t) ∈ E ∧
    ∀ e, spatial l t e ∈ Ico (spatial (center ρ q) t e + ρ * a e)
      (spatial (center ρ q) t e + ρ * a e + ρ * r)}) ?_) h
  intro l hl
  refine ⟨hl.1, fun e => ?_⟩
  apply subtract_div_mem_Ico hρ
  simpa only [← zoomSpatial_eq] using hl.2 e

/-- Smaller coefficient pieces are measured inside the unchanged coarse
block prior. A floor for their full original prior, together with a retained
intersection floor, pays for the conditional spatial cap. -/
theorem prior_piece_spatial_cap
    (θ : Measure ScalarLine) (E : Set ScalarIncidence) (t : ℝ)
    {ρ β δ r : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hr : 0 ≤ r)
    (q b : Fin 5 → ℤ) (C a η π : ENNReal)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (hη0 : η ≠ 0) (hηtop : η ≠ ⊤)
    (hcap : ∀ z, θ {l | (l, t) ∈ E ∧ cell β l.2 = b ∧ cell δ (spatial l t) = z} ≤ C * π)
    (hfloor : a * π ≤ θ {l | cell β l.2 = b})
    (hintersection : η * θ {l | cell β l.2 = b} ≤
      θ {l | cell β l.2 = b ∧ cell ρ l.2 = q}) (v : Fin 2 → ℝ) :
    prior θ ρ q {l | cell β l.2 = b ∧ (l, t) ∈ E ∧
      ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + r)} ≤
      ((ENNReal.ofReal ((ρ * r / δ + 2) ^ 2) * C) / (η * a)) *
        prior θ ρ q {l | cell β l.2 = b} := by
  let A : Set ScalarLine := {l | cell β l.2 = b ∧ (l, t) ∈ E ∧
    ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + r)}
  let B : Set ScalarLine := {l | cell β l.2 = b ∧ cell ρ l.2 = q}
  have hupper : θ (A ∩ {l | cell ρ l.2 = q}) ≤
      (ENNReal.ofReal ((ρ * r / δ + 2) ^ 2) * C) * π := by
    have h := zoom_cube_cap {p | p ∈ E ∧ cell β p.1.2 = b} t hρ hδ hr q (C * π)
      (fun z => by simpa only [mem_ofPred_eq, and_assoc] using hcap z) v
    apply (measure_mono (t := {l | (l, t) ∈ E ∧ cell β l.2 = b ∧
      ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + r)}) ?_).trans
    · simpa only [mem_ofPred_eq, and_assoc, mul_assoc] using h
    · intro l hl
      exact ⟨hl.1.2.1, hl.1.1, hl.1.2.2⟩
  have hlower : (η * a) * π ≤ θ B := by
    calc
      _ = η * (a * π) := by ring
      _ ≤ η * θ {l | cell β l.2 = b} := mul_le_mul_right hfloor η
      _ ≤ θ B := hintersection
  have hratio := cap_of_palette_floor (mul_ne_zero hη0 ha0)
    (ENNReal.mul_ne_top hηtop hatop) hupper hlower
  change prior θ ρ q A ≤ _
  simp only [prior, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (measurableSet_block ρ q)]
  have hB : {l | cell β l.2 = b} ∩ {l | cell ρ l.2 = q} = B := by
    ext l
    simp only [B, mem_inter_iff, mem_ofPred_eq]
  rw [hB]
  convert mul_le_mul_right hratio (θ {l | cell ρ l.2 = q})⁻¹ using 1; ring

end

end Zoom

end Submission.Obl.k4_scalar_grid_polynomial_qualification
