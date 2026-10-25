/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/TiltedMesh.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/TiltedMesh.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Submission.Lib.K4AngularCharge.ChartCells

/-! Original finite meshes covering a tilted true child box, with the thin side retained. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- The original point stays within one mesh width of its lower grid corner. -/
lemma floor_mesh_error {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |x - (⌊x / η⌋ : ℝ) * η| ≤ η := by
  have hlo : (⌊x / η⌋ : ℝ) * η ≤ x := (le_div_iff₀ hη).mp (Int.floor_le _)
  have hhi : x < ((⌊x / η⌋ : ℝ) + 1) * η :=
    (div_lt_iff₀ hη).mp (Int.lt_floor_add_one _)
  rw [abs_le]
  constructor <;> nlinarith

/-- Original isotropic mesh cells meeting a three-dimensional triangular box. -/
lemma exists_triangular_mesh_cells (t₀ z₀ y₀ l₁ l₂ l₃ R₀ R₁ R₂ η : ℝ)
    (hη : 0 < η) (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    ∃ V : Finset (Fin 3 → ℤ),
      (V.card : ℝ) ≤ (2 * R₀ / η + 2) * (2 * R₁ / η + 2 * |l₁| + 2) *
        (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) ∧
      ∀ t Z Y : ℝ, |t - t₀| ≤ R₀ → |Z - z₀ - l₁ * (t - t₀)| ≤ R₁ →
        |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ R₂ →
        (![⌊t / η⌋, ⌊Z / η⌋, ⌊Y / η⌋] : Fin 3 → ℤ) ∈ V := by
  classical
  obtain ⟨U, hUcard, hU⟩ := Submission.Lib.K4AngularCharge.exists_cells_tilted
    t₀ z₀ l₁ R₀ R₁ η hη hR₀ hR₁
  let d := R₂ + (|l₂| + |l₃|) * η
  let center : (Fin 2 → ℤ) → ℝ := fun u =>
    y₀ + l₂ * ((u 0 : ℝ) * η - t₀) + l₃ * ((u 1 : ℝ) * η - z₀)
  let W : (Fin 2 → ℤ) → Finset ℤ := fun u =>
    Finset.Icc ⌊(center u - d) / η⌋ ⌊(center u + d) / η⌋
  let V := U.biUnion (fun u => (W u).image (fun k => (![u 0, u 1, k] : Fin 3 → ℤ)))
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hW (u : Fin 2 → ℤ) : ((W u).card : ℝ) ≤
      2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2 := by
    have hle : (center u - d) / η ≤ (center u + d) / η :=
      div_le_div_of_nonneg_right (by linarith) hη.le
    have h := Submission.Lib.K4AngularCharge.card_Icc_floor_le _ _ hle
    have heq : (center u + d) / η - (center u - d) / η + 2 =
        2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2 := by
      dsimp [d]
      field_simp
      ring
    exact h.trans_eq heq
  refine ⟨V, ?_, ?_⟩
  · calc
      (V.card : ℝ) ≤ ∑ u ∈ U,
          (((W u).image (fun k => (![u 0, u 1, k] : Fin 3 → ℤ))).card : ℝ) := by
        dsimp only [V]
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ u ∈ U, ((W u).card : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        exact_mod_cast Finset.card_image_le
      _ ≤ ∑ _u ∈ U, (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) :=
        Finset.sum_le_sum (fun u _ => hW u)
      _ = (U.card : ℝ) * (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hUcard (by positivity)
  · intro t Z Y ht hZ hY
    let u : Fin 2 → ℤ := ![⌊t / η⌋, ⌊Z / η⌋]
    have hu : u ∈ U := hU t Z ht hZ
    have hround := floor_mesh_error hη
    have ht' : |l₂ * (t - (u 0 : ℝ) * η)| ≤ |l₂| * η := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hround t) (abs_nonneg _)
    have hZ' : |l₃ * (Z - (u 1 : ℝ) * η)| ≤ |l₃| * η := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hround Z) (abs_nonneg _)
    have hid : Y - center u =
        (Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)) +
        l₂ * (t - (u 0 : ℝ) * η) + l₃ * (Z - (u 1 : ℝ) * η) := by
      dsimp [center]
      ring
    have hband : |Y - center u| ≤ d := by
      rw [hid]
      have h := abs_add_le
        ((Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)) + l₂ * (t - (u 0 : ℝ) * η))
        (l₃ * (Z - (u 1 : ℝ) * η))
      have h' := abs_add_le (Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀))
        (l₂ * (t - (u 0 : ℝ) * η))
      dsimp [d]
      nlinarith
    have hYcell : ⌊Y / η⌋ ∈ W u := by
      apply Finset.mem_Icc.mpr
      constructor <;> apply Int.floor_le_floor <;>
        apply div_le_div_of_nonneg_right _ hη.le <;> linarith [abs_le.mp hband]
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨⌊Y / η⌋, hYcell, rfl⟩⟩

/-- If the mesh resolves all slopes and side lengths, its cell count has the
true three-dimensional volume bound, including the thin transverse side. -/
lemma exists_triangular_mesh_volume (t₀ z₀ y₀ l₁ l₂ l₃ R₀ R₁ R₂ η : ℝ)
    (hη : 0 < η) (hg₀ : η ≤ R₀) (hg₁ : (|l₁| + 1) * η ≤ R₁)
    (hg₂ : (|l₂| + |l₃| + 1) * η ≤ R₂) :
    ∃ V : Finset (Fin 3 → ℤ), (V.card : ℝ) * η ^ 3 ≤ 64 * R₀ * R₁ * R₂ ∧
      ∀ t Z Y : ℝ, |t - t₀| ≤ R₀ → |Z - z₀ - l₁ * (t - t₀)| ≤ R₁ →
        |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ R₂ →
        (![⌊t / η⌋, ⌊Z / η⌋, ⌊Y / η⌋] : Fin 3 → ℤ) ∈ V := by
  have hR₀ : 0 ≤ R₀ := hη.le.trans hg₀
  have hR₁ : 0 ≤ R₁ := (by positivity : 0 ≤ (|l₁| + 1) * η).trans hg₁
  have hR₂ : 0 ≤ R₂ := (by positivity : 0 ≤ (|l₂| + |l₃| + 1) * η).trans hg₂
  obtain ⟨V, hcard, hcover⟩ := exists_triangular_mesh_cells t₀ z₀ y₀ l₁ l₂ l₃
    R₀ R₁ R₂ η hη hR₀ hR₁ hR₂
  have h₀ : (2 * R₀ / η + 2) * η ≤ 4 * R₀ := by
    rw [add_mul, div_mul_cancel₀ _ hη.ne']
    linarith
  have h₁ : (2 * R₁ / η + 2 * |l₁| + 2) * η ≤ 4 * R₁ := by
    have heq : (2 * R₁ / η + 2 * |l₁| + 2) * η =
        2 * R₁ + 2 * ((|l₁| + 1) * η) := by field_simp; ring
    rw [heq]
    linarith
  have h₂ : (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) * η ≤ 4 * R₂ := by
    have heq : (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) * η =
        2 * R₂ + 2 * ((|l₂| + |l₃| + 1) * η) := by field_simp; ring
    rw [heq]
    linarith
  refine ⟨V, ?_, hcover⟩
  calc (V.card : ℝ) * η ^ 3 ≤
        ((2 * R₀ / η + 2) * (2 * R₁ / η + 2 * |l₁| + 2) *
          (2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2)) * η ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((2 * R₀ / η + 2) * η) * ((2 * R₁ / η + 2 * |l₁| + 2) * η) *
        ((2 * R₂ / η + 2 * (|l₂| + |l₃|) + 2) * η) := by ring
    _ ≤ (4 * R₀) * (4 * R₁) * (4 * R₂) :=
        mul_le_mul (mul_le_mul h₀ h₁ (by positivity) (by positivity)) h₂
          (by positivity) (by positivity)
    _ = _ := by ring

end Submission.Obl.k4_horizontal_strict_parameter_step
