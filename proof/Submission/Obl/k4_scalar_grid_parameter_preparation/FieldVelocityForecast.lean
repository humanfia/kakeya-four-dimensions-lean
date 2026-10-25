/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FieldVelocityForecast.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SnapshotCaps

/-! A steep almost-constant scalar field predicts velocity on an original incidence event. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

theorem velocity_diameter_of_affine_constraint (A B v w R M β : ℝ)
    (hM : 0 < M) (hB : M ≤ |B|) (hR : R ≤ M * β)
    (hv : |A + B * v| ≤ R) (hw : |A + B * w| ≤ R) : dist v w ≤ 2 * β := by
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M * dist v w ≤ |B| * dist v w := mul_le_mul_of_nonneg_right hB dist_nonneg
    _ = |(A + B * v) - (A + B * w)| := by
      rw [Real.dist_eq, ← abs_mul]
      congr 1
      ring
    _ ≤ |A + B * v| + |A + B * w| := abs_sub _ _
    _ ≤ R + R := add_le_add hv hw
    _ ≤ M * (2 * β) := by nlinarith

theorem steep_field_velocity_diameter {Ω : Type*} (C : Set Ω) (A B V : Ω → ℝ)
    (D K M β : ℝ) (hK : 0 ≤ K) (hM : 0 < M) (hbudget : D + 1 + K ≤ M * β)
    (hV : ∀ p ∈ C, |V p| ≤ K)
    (hdir : ∀ p ∈ C, |A p + B p * V p| ≤ D)
    (hsteep : ∀ p ∈ C, M ≤ |B p|)
    (hA : ∀ p ∈ C, ∀ p' ∈ C, |A p - A p'| ≤ 1)
    (hB : ∀ p ∈ C, ∀ p' ∈ C, |B p - B p'| ≤ 1) :
    ∀ p ∈ C, ∀ p' ∈ C, dist (V p) (V p') ≤ 2 * β := by
  intro p hp p' hp'
  have hfrozen : |A p + B p * V p'| ≤ D + 1 + K := by
    calc
      _ = |(A p' + B p' * V p') + (A p - A p') + (B p - B p') * V p'| := by
        congr 1
        ring
      _ ≤ |A p' + B p' * V p'| + |A p - A p'| + |(B p - B p') * V p'| :=
        abs_add_three _ _ _
      _ ≤ D + 1 + K := add_le_add (add_le_add (hdir p' hp') (hA p hp p' hp')) (by
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (hB p hp p' hp') (hV p' hp')
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  exact velocity_diameter_of_affine_constraint (A p) (B p) (V p) (V p')
    (D + 1 + K) M β hM (hsteep p hp) hbudget
    ((hdir p hp).trans (by linarith)) hfrozen

/-- A short velocity range meets only boundedly many original palette bins.  The
conditional incidence caps and angular caps are applied before any normalization. -/
theorem short_velocity_range_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → ℝ) (C : Set Ω) (π : Measure ℝ)
    (β : ℝ) (hβ : 0 < β) (J P : ℝ≥0∞)
    (hdiam : ∀ p ∈ C, ∀ p' ∈ C, dist (V p) (V p') ≤ 2 * β)
    (hjoint : ∀ c : ℤ, μ {p | p ∈ C ∧ V p ∈ scalarVelocityBin β c} ≤
      J * π (scalarVelocityBin β c))
    (hangular : ∀ c : ℤ, π (scalarVelocityBin β c) ≤ P) :
    μ C ≤ 400 * (J * P) := by
  apply two_coordinate_grid_mass_le μ V V (fun _ => 0) C Set.univ β 1 hβ (by norm_num) (J * P)
  · intro p hp p' hp'
    exact (hdiam p hp p' hp').trans (by linarith)
  · intro p hp p' hp'
    simp
  · intro p hp
    exact Set.mem_univ _
  · intro q a
    exact (measure_mono (by intro p hp; exact ⟨hp.1, hp.2.1⟩)).trans
      ((hjoint q).trans (mul_le_mul le_rfl (hangular q) bot_le bot_le))

theorem steep_field_original_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (A B V : Ω → ℝ) (π : Measure ℝ)
    (D K M β : ℝ) (hK : 0 ≤ K) (hM : 0 < M) (hβ : 0 < β)
    (hbudget : D + 1 + K ≤ M * β)
    (hV : ∀ p ∈ C, |V p| ≤ K)
    (hdir : ∀ p ∈ C, |A p + B p * V p| ≤ D)
    (hsteep : ∀ p ∈ C, M ≤ |B p|)
    (hA : ∀ p ∈ C, ∀ p' ∈ C, |A p - A p'| ≤ 1)
    (hB : ∀ p ∈ C, ∀ p' ∈ C, |B p - B p'| ≤ 1)
    (J P : ℝ≥0∞)
    (hjoint : ∀ c : ℤ, μ {p | p ∈ C ∧ V p ∈ scalarVelocityBin β c} ≤
      J * π (scalarVelocityBin β c))
    (hangular : ∀ c : ℤ, π (scalarVelocityBin β c) ≤ P) :
    μ C ≤ 400 * (J * P) :=
  short_velocity_range_mass_le μ V C π β hβ J P
    (steep_field_velocity_diameter C A B V D K M β hK hM hbudget hV hdir hsteep hA hB)
    hjoint hangular

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
