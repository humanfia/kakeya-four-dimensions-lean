/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/Inherited/ContactGrid.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/ContactGrid.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ContactGrid.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.ContactVolume
import Submission.Obl.k4_oss_weighted_level_transfer.Discretize
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking

/-! Whole fine cells meeting the common contact box have an H^4 volume budget. -/

namespace Submission.Obl.k4_critical_switching_state_preparation.Inherited

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

def contactGridCell (δ : ℝ) (j : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  {q | ∀ i, ⌊q i / δ⌋ = j i}

theorem measurableSet_contactGridCell (δ : ℝ) (j : Fin 3 → ℤ) :
    MeasurableSet (contactGridCell δ j) := by
  unfold contactGridCell
  measurability

theorem contactGridCell_eq_pi {δ : ℝ} (hδ : 0 < δ) (j : Fin 3 → ℤ) :
    contactGridCell δ j = Set.univ.pi
      (fun i => Set.Ico (δ * (j i : ℝ)) (δ * (j i : ℝ) + δ)) := by
  ext q
  simp only [Submission.Obl.k4_oss_weighted_level_transfer.Ico_eq_cell hδ,
    Submission.Obl.k4_oss_collision_cauchy_schwarz.cell, contactGridCell,
    mem_setOf_eq, mem_pi, mem_univ, forall_true_left]

theorem volume_contactGridCell {δ : ℝ} (hδ : 0 < δ) (j : Fin 3 → ℤ) :
    volume (contactGridCell δ j) = ENNReal.ofReal (δ ^ 3) := by
  rw [contactGridCell_eq_pi hδ, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hδ.le 3).symm

theorem contactGridCell_disjoint (δ : ℝ) :
    Pairwise (fun i j : Fin 3 → ℤ => Disjoint (contactGridCell δ i) (contactGridCell δ j)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun q hi hj => hij ?_
  exact funext fun k => (hi k).symm.trans (hj k)

theorem contactGridCell_coordinate_gap {δ : ℝ} (hδ : 0 < δ) {j : Fin 3 → ℤ}
    {q r : Fin 3 → ℝ} (hq : q ∈ contactGridCell δ j) (hr : r ∈ contactGridCell δ j)
    (i : Fin 3) : |q i - r i| ≤ δ :=
  Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq hδ
    ((hq i).trans (hr i).symm)

theorem mem_contactOuterBox_iff (m H A B : ℝ) (p q : Fin 3 → ℝ) :
    q ∈ contactOuterBox m p H A B ↔
      |q 0 - m| ≤ H / 2 ∧ |q 1 - referenceZ p (q 0)| ≤ A ∧
      |contactTransverse m p q| ≤ B := by
  change (![m - H / 2, -A, -B] ≤ contactCoordinates m p q ∧
    contactCoordinates m p q ≤ ![m + H / 2, A, B]) ↔ _
  constructor
  · intro h
    have h₀ := And.intro (h.1 0) (h.2 0)
    have h₁ := And.intro (h.1 1) (h.2 1)
    have h₂ := And.intro (h.1 2) (h.2 2)
    dsimp [contactCoordinates] at h₀ h₁ h₂
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr h₁, abs_le.mpr h₂⟩
  · rintro ⟨h₀, h₁, h₂⟩
    have ht := abs_le.mp h₀
    have hZ := abs_le.mp h₁
    have hY := abs_le.mp h₂
    constructor <;> intro i <;> fin_cases i <;> dsimp [contactCoordinates] <;> linarith

theorem contactTransverse_gap (m : ℝ) (p q r : Fin 3 → ℝ) :
    contactTransverse m p q - contactTransverse m p r =
      (q 2 - r 2) + (p 0 + m * p 2) * (q 0 - r 0) - m * (q 1 - r 1) := by
  unfold contactTransverse referenceY referenceZ
  ring

/-- Coordinatewise mesh error changes the two contact residuals by at most
2*K*delta and 3*K*delta. The large affine intercept cancels. -/
theorem contactCoordinates_mesh_gap (m K δ : ℝ) (p q r : Fin 3 → ℝ)
    (hK : 1 ≤ K) (hm : |m| ≤ 1) (hv : |p 2| ≤ K)
    (hcenter : |p 0 + m * p 2| ≤ K) (hgap : ∀ i, |q i - r i| ≤ δ) :
    |(q 1 - referenceZ p (q 0)) - (r 1 - referenceZ p (r 0))| ≤ 2 * K * δ ∧
    |contactTransverse m p q - contactTransverse m p r| ≤ 3 * K * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hgap 0)
  have hK0 : 0 ≤ K := by linarith
  constructor
  · calc
      _ = |(q 1 - r 1) - p 2 * (q 0 - r 0)| := by congr 1; unfold referenceZ; ring
      _ ≤ |q 1 - r 1| + |p 2 * (q 0 - r 0)| := abs_sub _ _
      _ ≤ δ + K * δ := add_le_add (hgap 1)
        (by rw [abs_mul]; exact mul_le_mul hv (hgap 0) (abs_nonneg _) hK0)
      _ ≤ _ := by nlinarith
  · rw [contactTransverse_gap]
    calc
      _ ≤ |q 2 - r 2| + |(p 0 + m * p 2) * (q 0 - r 0)| + |m * (q 1 - r 1)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ δ + K * δ + δ := by
        apply add_le_add
        · apply add_le_add (hgap 2)
          rw [abs_mul]
          exact mul_le_mul hcenter (hgap 0) (abs_nonneg _) hK0
        · rw [abs_mul]
          exact (mul_le_mul hm (hgap 1) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ ≤ _ := by nlinarith

/-- Every complete grid cell touching the common contact box stays in one
enlargement with the same H^4 scale, provided the mesh is at most H^2. -/
theorem contactGridCell_subset_enlargement {m H K δ : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H ^ 2)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    {j : Fin 3 → ℤ} {r : Fin 3 → ℝ} (hr : r ∈ contactGridCell δ j)
    (hrbox : r ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2)) :
    contactGridCell δ j ⊆ contactOuterBox m p (4 * H) (16 * K * H) (64 * K ^ 2 * H ^ 2) := by
  intro q hq
  have hδH' : δ ≤ H := hδH.trans (by nlinarith)
  have hK0 : 0 ≤ K := by linarith
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hrb := (mem_contactOuterBox_iff _ _ _ _ _ _).mp hrbox
  have hg := contactCoordinates_mesh_gap m K δ p q r hK hm hv hcenter
    (contactGridCell_coordinate_gap hδ hq hr)
  apply (mem_contactOuterBox_iff _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · calc
      |q 0 - m| ≤ |q 0 - r 0| + |r 0 - m| := by
        convert abs_add_le (q 0 - r 0) (r 0 - m) using 1 <;> congr 1 <;> ring
      _ ≤ δ + H / 2 := add_le_add (contactGridCell_coordinate_gap hδ hq hr 0) hrb.1
      _ ≤ _ := by linarith
  · calc
      _ ≤ |(q 1 - referenceZ p (q 0)) - (r 1 - referenceZ p (r 0))| +
        |r 1 - referenceZ p (r 0)| := by
          simpa only [sub_zero] using
            abs_sub_le (q 1 - referenceZ p (q 0)) (r 1 - referenceZ p (r 0)) 0
      _ ≤ 2 * K * δ + 8 * K * H := add_le_add hg.1 hrb.2.1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hδH' hK0]
  · calc
      _ ≤ |contactTransverse m p q - contactTransverse m p r| + |contactTransverse m p r| :=
        by simpa only [sub_zero] using abs_sub_le (contactTransverse m p q) (contactTransverse m p r) 0
      _ ≤ 3 * K * δ + 32 * K ^ 2 * H ^ 2 := add_le_add hg.2 hrb.2.2
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hδH hK0,
        mul_le_mul_of_nonneg_right hKsq (sq_nonneg H)]

/-- Count occupied fine codes by complete-cell volume, with no coordinate
bounding box that would discard the transverse H^2 scale. -/
theorem contactGrid_count {m H K δ : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H ^ 2)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (F : Finset (Fin 3 → ℤ))
    (hF : ∀ j ∈ F, (contactGridCell δ j ∩
      contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2)).Nonempty) :
    (F.card : ℝ) * δ ^ 3 ≤ 16384 * K ^ 3 * H ^ 4 := by
  have hsub : (⋃ j ∈ F, contactGridCell δ j) ⊆
      contactOuterBox m p (4 * H) (16 * K * H) (64 * K ^ 2 * H ^ 2) := by
    intro q hq
    rcases Set.mem_iUnion₂.mp hq with ⟨j, hj, hq⟩
    rcases hF j hj with ⟨r, hr, hrbox⟩
    exact contactGridCell_subset_enlargement hH hH1 hK hδ hδH hm hv hcenter hr hrbox hq
  have hvol := measure_mono (μ := (volume : Measure (Fin 3 → ℝ))) hsub
  rw [measure_biUnion_finset (fun j _ k _ hjk => contactGridCell_disjoint δ hjk)
    (fun j _ => measurableSet_contactGridCell δ j)] at hvol
  simp only [volume_contactGridCell hδ, Finset.sum_const, nsmul_eq_mul] at hvol
  have hK0 : 0 ≤ K := by linarith
  rw [volume_contactOuterBox _ _ _ _ _ (by positivity) (by positivity) (by positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)] at hvol
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤
      4 * (4 * H) * (16 * K * H) * (64 * K ^ 2 * H ^ 2))).mp hvol
  convert hr using 1 <;> ring

end

end Submission.Obl.k4_critical_switching_state_preparation.Inherited
