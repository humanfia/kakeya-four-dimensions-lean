-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalStateCanonicalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetWorldCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors

/-! Canonical moving-frame cells above an ordinary physical cell.
Adapted from `exists_original_fine_state_zoom_cells_of_jets` in this
obligation's FourJetWorldCells. The cell and query meshes may now agree;
the four central jets are paid in the explicit polynomial menu bound.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- An explicit carrier for the unit coefficient worlds of a bounded
original table. It does not depend on an evolving source. -/
def boundedUnitWorlds (H : ℕ) : Finset (Fin 7 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(H:ℤ)-1) ((H:ℤ)+1)

theorem boundedUnitWorlds_card (H : ℕ) :
    ((boundedUnitWorlds H).card : ℝ)=(2*(H:ℝ)+3)^7 := by
  have hlength : ((H:ℤ)+1)+1-(-(H:ℤ)-1)=(2*H+3:ℕ) := by omega
  simp only [boundedUnitWorlds,Fintype.card_piFinset,Int.card_Icc,hlength,
    Int.toNat_natCast,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  push_cast
  ring

theorem parameterCode_one_mem_boundedUnitWorlds (H : ℕ) (c : Fin 7 → ℝ)
    (hc : ∀ i, |c i| ≤ H) : parameterCode 1 c∈boundedUnitWorlds H := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hlo := Int.lt_floor_add_one (c i)
  have hhi := Int.floor_le (c i)
  have hb := abs_le.mp (hc i)
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : (-(H:ℝ)-1) ≤ (⌊c i⌋:ℝ) := by linarith only [hlo,hb.1]
    simpa only [parameterCode,div_one] using (by exact_mod_cast hh : -(H:ℤ)-1 ≤ ⌊c i⌋)
  · have hh : (⌊c i⌋:ℝ) ≤ (H:ℝ)+1 := by linarith only [hhi,hb.2]
    simpa only [parameterCode,div_one] using (by exact_mod_cast hh : ⌊c i⌋ ≤ (H:ℤ)+1)

/-- In a unit coefficient world, a physical cell at mesh `s` has only
polynomially many canonical cells at the SAME mesh. Intercepts do not
enter the bound. -/
theorem exists_original_state_canonical_menus {Λ W : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    (world : Λ → W) (center : W → Fin 7 → ℝ)
    {s K : ℝ} (hs : 0 < s) (hK : 0 ≤ K)
    (hcenter : ∀ z∈E, |center (world z.1) 1| ≤ K ∧ |center (world z.1) 2| ≤ K ∧
      |center (world z.1) 4| ≤ K ∧ |center (world z.1) 6| ≤ K)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1) :
    ∃ menus : ((Fin 4 → ℤ) × W) → Finset (Fin 4 → ℤ),
      (∀ key, ((menus key).card : ℝ) ≤ (6*K+6)^4) ∧
      ∀ z∈E, cell s (zpos (zoomCoefficients 1 (center (world z.1)) (c z.1)) z.2) ∈
        menus (originalFineState c s z,world z.1) := by
  classical
  let R := 2+3*K
  let Z := fun z : Λ × ℝ => zpos (zoomCoefficients 1 (center (world z.1)) (c z.1)) z.2
  let S := fun key : (Fin 4 → ℤ) × W =>
    {z∈E | originalFineState c s z=key.1 ∧ world z.1=key.2}
  have hf (key : (Fin 4 → ℤ) × W) :=
    Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card_of_relative_diameter
      (S key) Z (fun _ => s) R (fun _ => hs) (by dsimp [R]; positivity) (by
        intro i z hz z' hz'
        have hw : world z'.1=world z.1 := hz'.2.2.trans hz.2.2.symm
        have hcell : cell s (zpos (c z.1) z.2)=cell s (zpos (c z'.1) z'.2) :=
          hz.2.1.trans hz'.2.1.symm
        have hh := original_fine_cell_zoom_diameter_of_jets (c z.1) (c z'.1)
          (center (world z.1)) z.2 z'.2 s 1 (R*s) K hs (by norm_num) le_rfl hK
          (hcenter z hz.1) (ht z hz.1) (ht z' hz'.1)
          (by dsimp [R]; simp only [one_mul]; exact le_rfl) hcell i
        simpa only [Z,hw] using hh)
  let menus := fun key : (Fin 4 → ℤ) × W => (hf key).1.toFinset
  refine ⟨menus,?_,?_⟩
  · intro key
    have hh := (hf key).2
    rw [Set.ncard_eq_toFinset_card _ (hf key).1] at hh
    simpa only [menus,Fintype.card_fin,
      show 2*R+2=6*K+6 by dsimp [R]; ring] using hh
  · intro z hz
    apply (hf _).1.mem_toFinset.mpr
    exact ⟨z,⟨hz,rfl,rfl⟩,rfl⟩

/-- The actual unit coefficient centers inherit the original coefficient
bound. Thus ordinary cells can use the actual prepared canonical palettes. -/
theorem exists_canonical_unit_world_menus {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    (hc : ∀ z∈E, ∀ i, |c z.1 i| ≤ H)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1) :
    ∃ menus : ((Fin 4 → ℤ) × (Fin 7 → ℤ)) → Finset (Fin 4 → ℤ),
      (∀ key, ((menus key).card : ℝ) ≤ (6*H+12)^4) ∧
      ∀ z∈E, canonicalZoomCell c 1 s z ∈
        menus (originalFineState c s z,parameterCode 1 (c z.1)) := by
  have hcenter (z : Λ × ℝ) (hz : z∈E) :
      ∀ i, |parameterCenter 1 (parameterCode 1 (c z.1)) i| ≤ H+1 :=
    original_parameter_center_bound 1 H (by norm_num) le_rfl (c z.1) (hc z hz)
  obtain ⟨menus,hcard,hknown⟩ := exists_original_state_canonical_menus E c
    (fun l => parameterCode 1 (c l)) (parameterCenter 1) hs (by linarith)
    (fun z hz => ⟨hcenter z hz 1,hcenter z hz 2,hcenter z hz 4,hcenter z hz 6⟩) ht
  refine ⟨menus,?_,?_⟩
  · intro key
    convert hcard key using 1
    ring
  · exact hknown

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
