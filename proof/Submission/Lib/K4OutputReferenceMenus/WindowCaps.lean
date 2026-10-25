/-
The cell-dependent signal menu argument is adapted from this LOT tree,
o218, session x0764, branch x0764, commit6d7dae07757563e5448432607c4a813dd95dbce8,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/Grid.lean
(moving_cell_cap and moving_slab_cap). The base cover is imported from the
accepted K4MovingMeshBoxes contribution, so the mesh can absorb the shear
and the final volume constant is independent of its velocity bound.
-/
import Submission.Lib.K4MovingMeshBoxes.Geometry

namespace Submission.Lib.K4OutputReferenceMenus

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes

/-- Integrate native joint caps over a finite base table and a separate
finite signal menu for each native base cell. -/
theorem finite_moving_joint_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Fin 3 → ℤ) (signal : Ω → ℤ)
    (Q : Finset (Fin 3 → ℤ)) (J : (Fin 3 → ℤ) → Finset ℤ) (m : ℕ)
    (hJ : ∀ c ∈ Q, (J c).card ≤ m) (E : Set Ω)
    (hE : ∀ p ∈ E, code p ∈ Q ∧ signal p ∈ J (code p)) (L : ℝ≥0∞)
    (hcap : ∀ c j, μ {p | code p = c ∧ signal p = j} ≤ L) :
    μ E ≤ (Q.card : ℝ≥0∞) * m * L := by
  have hsub : E ⊆ ⋃ c ∈ Q, ⋃ j ∈ J c, {p | code p = c ∧ signal p = j} := by
    intro p hp
    obtain ⟨hc, hj⟩ := hE p hp
    exact mem_biUnion hc (mem_biUnion hj ⟨rfl, rfl⟩)
  calc
    _ ≤ μ (⋃ c ∈ Q, ⋃ j ∈ J c, {p | code p = c ∧ signal p = j}) := measure_mono hsub
    _ ≤ ∑ c ∈ Q, μ (⋃ j ∈ J c, {p | code p = c ∧ signal p = j}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ Q, ∑ j ∈ J c, μ {p | code p = c ∧ signal p = j} :=
      Finset.sum_le_sum (fun _ _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ c ∈ Q, (m : ℝ≥0∞) * L := by
      apply Finset.sum_le_sum
      intro c hc
      calc
        _ ≤ ∑ _j ∈ J c, L := Finset.sum_le_sum (fun j _ => hcap c j)
        _ = (J c).card * L := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul' (by exact_mod_cast hJ c hc) le_rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- A moving hidden window in an original base box is charged to the
literal native joint caps. The original palette factor is retained. -/
theorem moving_box_signal_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (offset : (Fin 3 → ℝ) → ℝ) (E : Set Ω)
    {δ a θ radius L C d : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hθ : 0 ≤ θ) (hθa : θ ≤ a)
    (hdr : δ ≤ radius) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, δ ≤ width i)
    (hmove : ∀ i, L * δ ≤ width i)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |point p i - y i| ≤ δ) → |offset (point p) - offset y| ≤ θ)
    (hE : ∀ p ∈ E, point p ∈ movingBox time radius center velocity width ∧
      offset (point p) ≤ value p ∧ value p ≤ offset (point p) + a)
    (weight : ℝ≥0∞)
    (hcap : ∀ c j, μ {p | baseMesh δ (point p) = c ∧ ⌊value p / a⌋ = j} ≤
      ENNReal.ofReal (C * δ ^ 3 * a ^ d) * weight) :
    μ E ≤ ENNReal.ofReal (6000 * C * radius * width 0 * width 1 * a ^ d) * weight := by
  classical
  obtain ⟨Q, hQcard, hQcover⟩ := movingBox_mesh_volume hδ hdr hL time center velocity width hv hdw hmove
  let anchor (c : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (c i : ℝ) * δ
  choose J hJcard hJcover using fun c : Fin 3 → ℤ =>
    interval_mesh_cover ha (show 0 ≤ 2 * a by positivity) (offset (anchor c))
  have hJ (c : Fin 3 → ℤ) : (J c).card ≤ 10 := by
    have hreal : ((J c).card : ℝ) ≤ 10 := by
      apply (hJcard c).trans_eq
      field_simp
      ring
    exact_mod_cast hreal
  have hcover (p : Ω) (hp : p ∈ E) :
      baseMesh δ (point p) ∈ Q ∧ ⌊value p / a⌋ ∈ J (baseMesh δ (point p)) := by
    refine ⟨hQcover _ (hE p hp).1, ?_⟩
    have hclose (i : Fin 3) :
        |point p i - anchor (baseMesh δ (point p)) i| ≤ δ := by
      have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (point p i / δ))
      have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (point p i / δ))
      dsimp only [anchor, baseMesh]
      rw [abs_le]
      constructor <;> nlinarith
    have hoff := ho p hp _ hclose
    have hval : |value p - offset (point p)| ≤ a := by
      rw [abs_le]
      constructor <;> linarith [(hE p hp).2.1, (hE p hp).2.2]
    apply hJcover
    calc
      _ ≤ |value p - offset (point p)| +
          |offset (point p) - offset (anchor (baseMesh δ (point p)))| := abs_sub_le _ _ _
      _ ≤ a + θ := add_le_add hval hoff
      _ ≤ _ := by linarith
  have hmass := finite_moving_joint_cap μ (fun p => baseMesh δ (point p))
    (fun p => ⌊value p / a⌋) Q J 10 (fun c _ => hJ c) E hcover
    (ENNReal.ofReal (C * δ ^ 3 * a ^ d) * weight) hcap
  have hreal : (Q.card : ℝ) * 10 * (C * δ ^ 3 * a ^ d) ≤
      6000 * C * radius * width 0 * width 1 * a ^ d := by
    calc
      _ = (10 * C * a ^ d) * ((Q.card : ℝ) * δ ^ 3) := by ring
      _ ≤ (10 * C * a ^ d) * (600 * radius * width 0 * width 1) :=
        mul_le_mul_of_nonneg_left hQcard (by positivity)
      _ = _ := by ring
  have heq : (Q.card : ℝ≥0∞) * 10 * ENNReal.ofReal (C * δ ^ 3 * a ^ d) =
      ENNReal.ofReal ((Q.card : ℝ) * 10 * (C * δ ^ 3 * a ^ d)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Q.card : ℝ) * 10),
      ENNReal.ofReal_mul (Nat.cast_nonneg Q.card)]
    norm_num
  calc
    _ ≤ (Q.card : ℝ≥0∞) * 10 * (ENNReal.ofReal (C * δ ^ 3 * a ^ d) * weight) := hmass
    _ = ENNReal.ofReal ((Q.card : ℝ) * 10 * (C * δ ^ 3 * a ^ d)) * weight := by
      rw [← heq]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

end Submission.Lib.K4OutputReferenceMenus
