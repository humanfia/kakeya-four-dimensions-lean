import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_native_grid_profile_extension.Dyadic

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Obl.k4_profile_density_bounds

/-- The nonnegative dyadic depth index. On the frozen depth rectangle the integer
floor in `width` is nonnegative, so this loses no information. -/
noncomputable abbrev depthIndex (n r : ℝ) : ℕ :=
  Submission.Obl.k4_native_grid_profile_extension.depthIndex n r

lemma depthIndex_mono {n r R : ℝ} (hn : 1 ≤ n) (hrR : r ≤ R) :
    depthIndex n r ≤ depthIndex n R :=
  Submission.Obl.k4_native_grid_profile_extension.depthIndex_mono hn hrR

lemma width_eq_inv_pow {n r : ℝ} (hn : 1 ≤ n) (hr : 0 ≤ r) :
    width n r = ((2 : ℝ) ^ depthIndex n r)⁻¹ :=
  Submission.Obl.k4_native_grid_profile_extension.dyadicWidth_eq_inv_pow hn hr

/-- The hidden or velocity bin at a coarser frozen depth is an exact integer quotient
of the finest bin. This also holds at negative spatial coordinates. -/
lemma native_bin_refinement {n r R : ℝ} (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hrR : r ≤ R) (x : ℝ) :
    ⌊x / width n r⌋ =
      ⌊x / width n R⌋ / (2 : ℤ) ^ (depthIndex n R - depthIndex n r) :=
  Submission.Obl.k4_native_grid_profile_extension.floor_dyadicWidth_refinement hn hr hrR x

/-- The exact six integer floors used in the frozen common label. -/
noncomputable def commonFloorLabel (n : ℝ) (H : ℕ) (R U : ℝ) (p : State) : Fin 6 → ℤ :=
  ![⌊n ^ H * base p 0⌋, ⌊n ^ H * base p 1⌋, ⌊n ^ H * base p 2⌋,
    ⌊hidden p / width n R⌋, ⌊velocity p.1 0 / width n U⌋,
    ⌊velocity p.1 1 / width n U⌋]

lemma commonFloorLabel_base (n : ℝ) (H : ℕ) (R U : ℝ) (p : State) (j : Fin 3) :
    commonFloorLabel n H R U p (j.castAdd 3) = ⌊n ^ H * base p j⌋ := by
  fin_cases j <;> rfl

/-- A canonical base point in a mesh cell, used only to define the value of the table. -/
noncomputable def commonBaseCorner (n : ℝ) (H : ℕ) (z : Fin 6 → ℤ) : Base :=
  WithLp.toLp 2 (fun j : Fin 3 => (z (j.castAdd 3) : ℝ) / n ^ H)

lemma commonBaseCorner_floor {n : ℝ} (hn : n ≠ 0) (H : ℕ)
    (z : Fin 6 → ℤ) (j : Fin 3) :
    ⌊n ^ H * commonBaseCorner n H z j⌋ = z (j.castAdd 3) := by
  change ⌊n ^ H * ((z (j.castAdd 3) : ℝ) / n ^ H)⌋ = _
  rw [mul_div_cancel₀ _ (pow_ne_zero H hn), Int.floor_intCast]

/-- A function on observations that is constant on continuous base mesh cells. -/
def ObservationBaseMeshConstant {α : Type*} (n : ℝ) (H : ℕ)
    (F : Observation → α) : Prop :=
  ∀ (b b' : Base) (h : ℤ) (v : Fin 2 → ℤ),
    (∀ j, ⌊n ^ H * b j⌋ = ⌊n ^ H * b' j⌋) → F ((b, h), v) = F ((b', h), v)

/-- The observation table on the common finest integer label. -/
noncomputable def commonLabelTable {α : Type*} (n : ℝ) (H : ℕ) (R U r u : ℝ)
    (F : Observation → α) (z : Fin 6 → ℤ) : α :=
  F ((commonBaseCorner n H z,
      z 3 / (2 : ℤ) ^ (depthIndex n R - depthIndex n r)),
    ![z 4 / (2 : ℤ) ^ (depthIndex n U - depthIndex n u),
      z 5 / (2 : ℤ) ^ (depthIndex n U - depthIndex n u)])

/-- One common finest floor label determines every coarser observation density
whose continuous coordinates have been flattened on the base mesh. -/
theorem common_label_factorization {α : Type*} {n : ℝ} (hn : 2 ≤ n)
    (H : ℕ) {R U r u : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hu : 0 ≤ u) (huU : u ≤ U) (F : Observation → α)
    (hF : ObservationBaseMeshConstant n H F) (p : State) :
    F (observe n r u p) =
      commonLabelTable n H R U r u F (commonFloorLabel n H R U p) := by
  have hn1 : 1 ≤ n := by linarith
  have hn0 : n ≠ 0 := by linarith
  have hh : ⌊hidden p / width n r⌋ = commonFloorLabel n H R U p 3 /
      (2 : ℤ) ^ (depthIndex n R - depthIndex n r) :=
    native_bin_refinement hn1 hr hrR (hidden p)
  have hv : (fun j : Fin 2 => ⌊velocity p.1 j / width n u⌋) =
      ![commonFloorLabel n H R U p 4 / (2 : ℤ) ^ (depthIndex n U - depthIndex n u),
        commonFloorLabel n H R U p 5 / (2 : ℤ) ^ (depthIndex n U - depthIndex n u)] := by
    funext j
    fin_cases j
    · exact native_bin_refinement hn1 hu huU (velocity p.1 0)
    · exact native_bin_refinement hn1 hu huU (velocity p.1 1)
  change F ((base p, ⌊hidden p / width n r⌋), _) = _
  rw [hh, hv]
  apply hF
  intro j
  rw [commonBaseCorner_floor hn0, commonFloorLabel_base]

/-- Pointwise global bounds on a flattened density are inherited by every table entry. -/
lemma commonLabelTable_bound {n : ℝ} (H : ℕ) (R U r u C : ℝ)
    (F : Observation → ℝ) (hF : ∀ y, 0 ≤ F y ∧ F y ≤ C) (z : Fin 6 → ℤ) :
    0 ≤ commonLabelTable n H R U r u F z ∧ commonLabelTable n H R U r u F z ≤ C :=
  hF _

end Submission.Obl.k4_native_base_flattening
