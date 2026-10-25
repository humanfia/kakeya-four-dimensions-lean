-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomFineStateCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomFineStateCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomFineStateCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomFineStateCells.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom
import Submission.Lib.K4CommonLocalChoice
import Submission.Lib.K4QuadraticSheets.JetBins
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- The central curve has speed bounded using its actual coefficients. -/
theorem central_curve_coordinate_lipschitz (c : Fin 7 → ℝ) (K t u : ℝ)
    (hK : 0 ≤ K) (hc : ∀ i, |c i| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    ∀ i : Fin 4, |zpos c t i - zpos c u i| ≤ (1+3*K)*|t-u| := by
  have hsum : |t+u| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ht.1 hu.1)]
    linarith [ht.2,hu.2]
  have hx : |zx c t-zx c u| ≤ 3*K*|t-u| := by
    rw [show zx c t-zx c u = (c 1+c 2*(t+u))*(t-u) by unfold zx; ring,abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    calc
      _ ≤ |c 1| + |c 2| * |t+u| := by simpa only [abs_mul] using abs_add_le (c 1) (c 2*(t+u))
      _ ≤ K+K*2 := add_le_add (hc 1) (mul_le_mul (hc 2) hsum (abs_nonneg _) hK)
      _ = 3*K := by ring
  have hy (a d : Fin 7) :
      |(c a+c d*t)-(c a+c d*u)| ≤ K*|t-u| := by
    rw [show (c a+c d*t)-(c a+c d*u)=c d*(t-u) by ring,abs_mul]
    exact mul_le_mul_of_nonneg_right (hc d) (abs_nonneg _)
  intro i
  fin_cases i
  · change |t-u| ≤ _
    nlinarith [abs_nonneg (t-u)]
  · change |zx c t-zx c u| ≤ _
    nlinarith [abs_nonneg (t-u)]
  · change |(c 3+c 4*t)-(c 3+c 4*u)| ≤ _
    have hh := hy 3 4
    nlinarith [abs_nonneg (t-u)]
  · change |(c 5+c 6*t)-(c 5+c 6*u)| ≤ _
    have hh := hy 5 6
    nlinarith [abs_nonneg (t-u)]

/-- An original fine cell has small diameter in its true parameter zoom.
Time retains its original units; only the three spatial coordinates scale. -/
theorem original_fine_cell_zoom_diameter (c c' center : Fin 7 → ℝ)
    (t u b ρ s K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hK : 0 ≤ K)
    (hc : ∀ i, |center i| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hsmall : (2+3*K)*b ≤ ρ*s)
    (hcell : Submission.Lib.K4CommonLocalChoice.cell b (zpos c t) =
      Submission.Lib.K4CommonLocalChoice.cell b (zpos c' u)) :
    ∀ i : Fin 4, |zpos (zoomCoefficients ρ center c) t i -
      zpos (zoomCoefficients ρ center c') u i| ≤ s := by
  have hgap (i : Fin 4) : |zpos c t i-zpos c' u i| ≤ b :=
    (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hb (congrFun hcell i)).le
  have htime : |t-u| ≤ b := hgap 0
  have hspeed := central_curve_coordinate_lipschitz center K t u hK hc ht hu
  have hcenter (i : Fin 4) : |zpos center t i-zpos center u i| ≤ (1+3*K)*b :=
    (hspeed i).trans (mul_le_mul_of_nonneg_left htime (by positivity))
  have hscaled (i : Fin 4) :
      |((zpos c t i-zpos center t i)-(zpos c' u i-zpos center u i))/ρ| ≤ s := by
    rw [abs_div,abs_of_pos hρ]
    apply (div_le_iff₀ hρ).mpr
    calc
      _ = |(zpos c t i-zpos c' u i)-(zpos center t i-zpos center u i)| := by congr 1; ring
      _ ≤ |zpos c t i-zpos c' u i|+|zpos center t i-zpos center u i| := abs_sub _ _
      _ ≤ b+(1+3*K)*b := add_le_add (hgap i) (hcenter i)
      _ ≤ s*ρ := by nlinarith [hsmall]
  have hs : b ≤ s := by
    have hsb : b ≤ ρ*s := by nlinarith [mul_nonneg hK hb.le]
    have hs0 : 0 ≤ s := by nlinarith
    exact hsb.trans (mul_le_of_le_one_left hs0 hρ1)
  intro i
  fin_cases i
  · exact htime.trans hs
  · simpa [zpos,zx_zoom,sub_div] using hscaled 1
  · simpa [zpos,zy_zoom,sub_div] using hscaled 2
  · simpa [zpos,zy_zoom,sub_div] using hscaled 3

/-- Each actual original fine state meets at most 256 zoomed cells in
one full original parameter world. The list covers the entire arbitrary
original line family and uses no finite approximation of its prior. -/
theorem exists_original_fine_state_zoom_cells_on_active_worlds {Λ W : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (world : Λ → W) (center : W → Fin 7 → ℝ)
    (b ρ s K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hK : 0 ≤ K)
    (hc : ∀ z ∈ E, ∀ i, |center (world z.1) i| ≤ K)
    (ht : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1) (hsmall : (2+3*K)*b ≤ ρ*s) :
    ∃ lists : (Fin 4 → ℤ) × W → Finset (Fin 4 → ℤ),
      (∀ q, (lists q).card ≤ 256) ∧
      ∀ z ∈ E, Submission.Lib.K4CommonLocalChoice.cell s
        (zpos (zoomCoefficients ρ (center (world z.1)) (c z.1)) z.2) ∈
        lists (Submission.Lib.K4CommonLocalChoice.cell b (zpos (c z.1) z.2),world z.1) := by
  classical
  let Z := fun z : Λ × ℝ => zpos (zoomCoefficients ρ (center (world z.1)) (c z.1)) z.2
  let S := fun q : (Fin 4 → ℤ) × W =>
    {z ∈ E | Submission.Lib.K4CommonLocalChoice.cell b (zpos (c z.1) z.2)=q.1 ∧ world z.1=q.2}
  have hf (q : (Fin 4 → ℤ) × W) :=
    Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card_of_relative_diameter
      (S q) Z (fun _ => s) 1 (fun _ => hs) (by norm_num) (by
        intro i z hz z' hz'
        have hw : world z'.1 = world z.1 := hz'.2.2.trans hz.2.2.symm
        have hh := original_fine_cell_zoom_diameter (c z.1) (c z'.1) (center (world z.1))
          z.2 z'.2 b ρ s K hb hρ hρ1 hK (hc z hz.1) (ht z hz.1) (ht z' hz'.1) hsmall
          (hz.2.1.trans hz'.2.1.symm) i
        simpa only [Z,hw,one_mul] using hh)
  let C (q : (Fin 4 → ℤ) × W) := (hf q).1.toFinset
  refine ⟨C,?_,?_⟩
  · intro q
    have hh := (hf q).2
    rw [Set.ncard_eq_toFinset_card _ (hf q).1] at hh
    norm_num at hh
    exact_mod_cast hh
  · intro z hz
    apply (hf _).1.mem_toFinset.mpr
    exact ⟨z,⟨hz,rfl,rfl⟩,rfl⟩

/-- Uniform central coefficients are a convenient special case. -/
theorem exists_original_fine_state_zoom_cells {Λ W : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (world : Λ → W) (center : W → Fin 7 → ℝ)
    (b ρ s K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hK : 0 ≤ K)
    (hc : ∀ w i, |center w i| ≤ K)
    (ht : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1) (hsmall : (2+3*K)*b ≤ ρ*s) :
    ∃ lists : (Fin 4 → ℤ) × W → Finset (Fin 4 → ℤ),
      (∀ q, (lists q).card ≤ 256) ∧
      ∀ z ∈ E, Submission.Lib.K4CommonLocalChoice.cell s
        (zpos (zoomCoefficients ρ (center (world z.1)) (c z.1)) z.2) ∈
        lists (Submission.Lib.K4CommonLocalChoice.cell b (zpos (c z.1) z.2),world z.1) :=
  exists_original_fine_state_zoom_cells_on_active_worlds E c world center b ρ s K
    hb hρ hρ1 hs hK (fun z _ => hc (world z.1)) ht hsmall

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
