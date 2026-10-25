-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetWorldCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetWorldCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit a194894209bc49bb7eab8e89d27e5205146250d6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetWorldCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomFineStateCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoefficientWorld
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CoarseGeometry

/-! # Parameter-world cell menus with arbitrary central intercepts

The cell argument adapts this obligation's ZoomFineStateCells.lean,
from x0943 at e4fad27e0. Only central curve speed is used; the four
central jets suffice and no bound on its three intercepts is imposed.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Lib.K4CommonLocalChoice
noncomputable section

theorem central_curve_coordinate_lipschitz_of_jets (c : Fin 7 → ℝ) (K t u : ℝ)
    (hK : 0 ≤ K) (hc : |c 1| ≤ K ∧ |c 2| ≤ K ∧ |c 4| ≤ K ∧ |c 6| ≤ K)
    (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) (i : Fin 4) :
    |zpos c t i-zpos c u i| ≤ (1+3*K)*|t-u| := by
  have hd : zpos c t i-zpos c u i=
      zpos (tangentCoefficients c) t i-zpos (tangentCoefficients c) u i := by
    fin_cases i <;> simp [zpos,zx,zy,tangentCoefficients] <;> ring
  rw [hd]
  exact central_curve_coordinate_lipschitz (tangentCoefficients c) K t u
    hK (tangentCoefficients_bound hK hc) ht hu i

theorem original_fine_cell_zoom_diameter_of_jets (c c' center : Fin 7 → ℝ)
    (t u b ρ s K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hK : 0 ≤ K)
    (hc : |center 1| ≤ K ∧ |center 2| ≤ K ∧ |center 4| ≤ K ∧ |center 6| ≤ K)
    (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
    (hsmall : (2+3*K)*b ≤ ρ*s) (hcell : cell b (zpos c t)=cell b (zpos c' u)) :
    ∀ i, |zpos (zoomCoefficients ρ center c) t i-
      zpos (zoomCoefficients ρ center c') u i| ≤ s := by
  have hgap (i : Fin 4) : |zpos c t i-zpos c' u i| ≤ b :=
    (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hb (congrFun hcell i)).le
  have htime : |t-u| ≤ b := hgap 0
  have hcenter (i : Fin 4) : |zpos center t i-zpos center u i| ≤ (1+3*K)*b :=
    (central_curve_coordinate_lipschitz_of_jets center K t u hK hc ht hu i).trans
      (mul_le_mul_of_nonneg_left htime (by positivity))
  have hscaled (i : Fin 4) :
      |((zpos c t i-zpos center t i)-(zpos c' u i-zpos center u i))/ρ| ≤ s := by
    rw [abs_div,abs_of_pos hρ]
    apply (div_le_iff₀ hρ).mpr
    calc
      _ = |(zpos c t i-zpos c' u i)-(zpos center t i-zpos center u i)| := by congr 1; ring
      _ ≤ |zpos c t i-zpos c' u i|+|zpos center t i-zpos center u i| := abs_sub _ _
      _ ≤ b+(1+3*K)*b := add_le_add (hgap i) (hcenter i)
      _ ≤ s*ρ := by nlinarith only [hsmall]
  have hs : b ≤ s := by
    have hsb : b ≤ ρ*s := by nlinarith only [hsmall,mul_nonneg hK hb.le,hb.le]
    have hs0 : 0 ≤ s := by nlinarith only [hsb,hρ,hb]
    exact hsb.trans (mul_le_of_le_one_left hs0 hρ1)
  intro i
  fin_cases i
  · exact htime.trans hs
  · simpa [zpos,zx_zoom,sub_div] using hscaled 1
  · change |zy (zoomCoefficients ρ center c) t 0-zy (zoomCoefficients ρ center c') u 0| ≤ s
    simp only [zy_zoom]
    have hh : |((zy c t 0-zy center t 0)-(zy c' u 0-zy center u 0))/ρ| ≤ s := hscaled 2
    simpa only [sub_div] using hh
  · change |zy (zoomCoefficients ρ center c) t 1-zy (zoomCoefficients ρ center c') u 1| ≤ s
    simp only [zy_zoom]
    have hh : |((zy c t 1-zy center t 1)-(zy c' u 1-zy center u 1))/ρ| ≤ s := hscaled 3
    simpa only [sub_div] using hh

/-- At most 256 transformed states lie above each original fine state
and fixed coefficient world, even if its central height is arbitrarily
large. The trajectory family and its tags remain arbitrary. -/
theorem exists_original_fine_state_zoom_cells_of_jets {Λ W : Type*}
    (E : Set (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) (world : Λ → W) (center : W → Fin 7 → ℝ)
    (b ρ s K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hK : 0 ≤ K)
    (hc : ∀ z ∈ E, |center (world z.1) 1| ≤ K ∧ |center (world z.1) 2| ≤ K ∧
      |center (world z.1) 4| ≤ K ∧ |center (world z.1) 6| ≤ K)
    (ht : ∀ z ∈ E, z.2 ∈ Icc (0:ℝ) 1) (hsmall : (2+3*K)*b ≤ ρ*s) :
    ∃ lists : (Fin 4 → ℤ)×W → Finset (Fin 4 → ℤ),
      (∀ q, (lists q).card ≤ 256) ∧
      ∀ z ∈ E, cell s (zpos (zoomCoefficients ρ (center (world z.1)) (c z.1)) z.2) ∈
        lists (cell b (zpos (c z.1) z.2),world z.1) := by
  classical
  let Z := fun z : Λ×ℝ => zpos (zoomCoefficients ρ (center (world z.1)) (c z.1)) z.2
  let S := fun q : (Fin 4 → ℤ)×W =>
    {z ∈ E | cell b (zpos (c z.1) z.2)=q.1 ∧ world z.1=q.2}
  have hf (q : (Fin 4 → ℤ)×W) :=
    Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card_of_relative_diameter
      (S q) Z (fun _ => s) 1 (fun _ => hs) (by norm_num) (by
        intro i z hz z' hz'
        have hw : world z'.1=world z.1 := hz'.2.2.trans hz.2.2.symm
        have hh := original_fine_cell_zoom_diameter_of_jets (c z.1) (c z'.1) (center (world z.1))
          z.2 z'.2 b ρ s K hb hρ hρ1 hK (hc z hz.1) (ht z hz.1) (ht z' hz'.1) hsmall
          (hz.2.1.trans hz'.2.1.symm) i
        simpa only [Z,hw,one_mul] using hh)
  let C (q : (Fin 4 → ℤ)×W) := (hf q).1.toFinset
  refine ⟨C,?_,?_⟩
  · intro q
    have hh := (hf q).2
    rw [Set.ncard_eq_toFinset_card _ (hf q).1] at hh
    norm_num at hh
    exact_mod_cast hh
  · intro z hz
    apply (hf _).1.mem_toFinset.mpr
    exact ⟨z,⟨hz,rfl,rfl⟩,rfl⟩

theorem coefficient_center_component_bound {n : ℕ} (c : Fin n → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (e : Fin n) :
    |CoefficientWorld.center ρ (cell ρ c) e| ≤ |c e|+ρ := by
  have hlo := (le_div_iff₀ hρ).mp (Int.floor_le (c e/ρ))
  have hhi := (div_lt_iff₀ hρ).mp (Int.lt_floor_add_one (c e/ρ))
  change |(⌊c e/ρ⌋:ℝ)*ρ| ≤ |c e|+ρ
  apply abs_le.mpr
  constructor
  · nlinarith only [hhi,neg_abs_le (c e)]
  · exact hlo.trans ((le_abs_self _).trans (le_add_of_nonneg_right hρ.le))

/-- The actual full coefficient-bin centers inherit just the four jet
bounds. No finite global range of the large intercept is needed. -/
theorem exists_coefficient_world_cell_menus {Λ : Type*}
    (E : Set (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) {b ρ s H : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hH : 0 ≤ H)
    (hc : ∀ z ∈ E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧ |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H)
    (ht : ∀ z ∈ E, z.2 ∈ Icc (0:ℝ) 1) (hsmall : (2+3*(H+1))*b ≤ ρ*s) :
    ∃ lists : (Fin 4 → ℤ)×(Fin 7 → ℤ) → Finset (Fin 4 → ℤ),
      (∀ q, (lists q).card ≤ 256) ∧
      ∀ z ∈ E, cell s (zpos (CoefficientWorld.coeff c ρ (cell ρ (c z.1)) z.1) z.2) ∈
        lists (cell b (zpos (c z.1) z.2),cell ρ (c z.1)) := by
  apply exists_original_fine_state_zoom_cells_of_jets E c (fun l => cell ρ (c l))
    (CoefficientWorld.center ρ) b ρ s (H+1) hb hρ hρ1 hs (by linarith) _ ht hsmall
  intro z hz
  have hh (e : Fin 7) (he : |c z.1 e| ≤ H) :
      |CoefficientWorld.center ρ (cell ρ (c z.1)) e| ≤ H+1 :=
    (coefficient_center_component_bound (c z.1) hρ e).trans (add_le_add he hρ1)
  exact ⟨hh 1 (hc z hz).1,hh 2 (hc z hz).2.1,
    hh 4 (hc z hz).2.2.1,hh 6 (hc z hz).2.2.2⟩

theorem scalar_cell_eq_physical_code {Λ : Type*} (c : Λ → Fin 7 → ℝ) (b : ℝ) (z : Λ×ℝ) :
    cell b (zpos (c z.1) z.2)=
      ![coefficientGridCode c b b z 0,coefficientGridCode c b b z 3,
        coefficientGridCode c b b z 1,coefficientGridCode c b b z 2] := by
  funext j
  fin_cases j <;> rfl

/-- The input state is written in the physical ordering `(t,y₀,y₁,X)`
used by the clock-parent count. The output cells have the scalar-normal
ordering `(t,X,y₀,y₁)`; the finite ambiguity remains 256. -/
theorem exists_coefficient_world_physical_cell_menus {Λ : Type*}
    (E : Set (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) {b ρ s H : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hH : 0 ≤ H)
    (hc : ∀ z ∈ E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧ |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H)
    (ht : ∀ z ∈ E, z.2 ∈ Icc (0:ℝ) 1) (hsmall : (2+3*(H+1))*b ≤ ρ*s) :
    ∃ lists : (Fin 4 → ℤ)×(Fin 7 → ℤ) → Finset (Fin 4 → ℤ),
      (∀ q, (lists q).card ≤ 256) ∧
      ∀ z ∈ E, cell s (zpos (CoefficientWorld.coeff c ρ (cell ρ (c z.1)) z.1) z.2) ∈
        lists (coefficientGridCode c b b z,cell ρ (c z.1)) := by
  obtain ⟨lists,hcard,hcover⟩ :=
    exists_coefficient_world_cell_menus E c hb hρ hρ1 hs hH hc ht hsmall
  let permute (q : Fin 4 → ℤ) : Fin 4 → ℤ := ![q 0,q 3,q 1,q 2]
  let physicalLists (q : (Fin 4 → ℤ)×(Fin 7 → ℤ)) := lists (permute q.1,q.2)
  refine ⟨physicalLists,fun q => hcard _,?_⟩
  intro z hz
  have hh := hcover z hz
  rw [scalar_cell_eq_physical_code] at hh
  exact hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
