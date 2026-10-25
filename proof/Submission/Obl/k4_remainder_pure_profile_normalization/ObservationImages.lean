/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/ObservationImages.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.SigmaFormat
import Submission.Obl.k4_native_grid_profile_extension.Observation

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set

/-- A floor observation is continuous on each of countably many half-open
strips.  Images of sigma-compact sets therefore remain sigma compact.
-/
theorem sigmaCompact_floor_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PerfectlyNormalSpace X] {F : Set X} (hF : IsSigmaCompact F)
    {u : X → Y} (hu : Continuous u) {w : X → ℝ} (hw : Continuous w) :
    IsSigmaCompact ((fun x => (u x, ⌊w x⌋)) '' F) := by
  let S (k : ℤ) : Set X := F ∩ {x | (k : ℝ) ≤ w x ∧ w x < (k : ℝ) + 1}
  let g (k : ℤ) (x : X) : Y × ℤ := (u x, k)
  have hS (k : ℤ) : IsSigmaCompact (S k) := by
    have heq : S k = (F ∩ {x | (k : ℝ) ≤ w x}) ∩ {x | w x < (k : ℝ) + 1} := by
      ext x
      simp only [S, mem_inter_iff, mem_ofPred_eq, and_assoc]
    rw [heq]
    exact sigmaCompact_inter_open
      (sigmaCompact_inter_closed hF (isClosed_le continuous_const hw))
      (isOpen_lt hw continuous_const)
  have heq : (fun x => (u x, ⌊w x⌋)) '' F = ⋃ k : ℤ, g k '' S k := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_iUnion.mpr ⟨⌊w x⌋, x, ⟨hx, Int.floor_le _, Int.lt_floor_add_one _⟩, rfl⟩
    · intro hz
      obtain ⟨k, x, ⟨hx, hl, hh⟩, rfl⟩ := mem_iUnion.mp hz
      have hfloor : ⌊w x⌋ = k := Int.floor_eq_iff.mpr ⟨hl, hh⟩
      exact ⟨x, hx, by simp only [hfloor, g]⟩
  rw [heq]
  exact isSigmaCompact_iUnion _ (fun k => (hS k).image (hu.prodMk continuous_const))

def incidenceSection (i : ℕ) (z : Fin 7 → ℝ) : Incidence :=
  ((i, fun j : Fin 6 => z j.castSucc), z 6)

theorem continuous_incidenceSection (i : ℕ) : Continuous (incidenceSection i) := by
  unfold incidenceSection
  fun_prop

theorem incidenceSection_lastCases (p : Incidence) :
    incidenceSection p.1.1 (Fin.lastCases p.2 p.1.2) = p := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      simp [incidenceSection]
  · change Fin.lastCases p.2 p.1.2 (Fin.last 6) = p.2
    exact Fin.lastCases_last

/-- The unobserved natural index costs only a countable union of sections. -/
theorem incidence_sigmaCompact_of_sections {F : Set Incidence}
    (hF : ∀ i : ℕ, IsSigmaCompact {z : Fin 7 → ℝ | incidenceSection i z ∈ F}) :
    IsSigmaCompact F := by
  have heq : F = ⋃ i : ℕ, incidenceSection i '' {z | incidenceSection i z ∈ F} := by
    ext p
    constructor
    · intro hp
      refine mem_iUnion.mpr ⟨p.1.1, Fin.lastCases p.2 p.1.2, ?_, incidenceSection_lastCases p⟩
      change incidenceSection p.1.1 (Fin.lastCases p.2 p.1.2) ∈ F
      rw [incidenceSection_lastCases]
      exact hp
    · intro hp
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hp
      exact hz
  rw [heq]
  exact isSigmaCompact_iUnion _ (fun i => (hF i).image (continuous_incidenceSection i))

theorem fmt_incidence_sigmaCompact {F : Set Incidence} {H : ℝ} {D : ℕ}
    (hF : ∀ i : ℕ, fmt 7 H D {z : Fin 7 → ℝ | incidenceSection i z ∈ F}) :
    IsSigmaCompact F :=
  incidence_sigmaCompact_of_sections (fun i => fmt_sigmaCompact (hF i))

/-- Native observation images are Borel for every event in the frozen format. -/
theorem obs_image_sigmaCompact (B a : ℝ) {F : Set Incidence} (hF : IsSigmaCompact F) :
    IsSigmaCompact (obs B a '' F) := by
  have hw : Continuous (fun p : Incidence => (x p.1 p.2) (3 : Fin 4)) :=
    (continuous_apply (3 : Fin 4)).comp
      Submission.Obl.k4_native_grid_profile_extension.continuous_trajectoryPoint
  exact sigmaCompact_floor_image hF
    Submission.Obl.k4_native_grid_profile_extension.continuous_baseObservation
    ((continuous_const.mul hw).div_const a)

theorem measurableSet_obs_image (B a : ℝ) {F : Set Incidence} {H : ℝ} {D : ℕ}
    (hF : ∀ i : ℕ, fmt 7 H D {z : Fin 7 → ℝ | incidenceSection i z ∈ F}) :
    MeasurableSet (obs B a '' F) :=
  measurableSet_of_sigmaCompact (obs_image_sigmaCompact B a (fmt_incidence_sigmaCompact hF))

theorem Chart.obs_image_measurable {Nk κ j r Bv : ℝ} {M D T : ℕ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (hc : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) (B a : ℝ) :
    MeasurableSet (obs B a '' F) := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
  exact measurableSet_obs_image B a (fun i => (hfmt i).2)

end Submission.Obl.k4_remainder_pure_profile_normalization
