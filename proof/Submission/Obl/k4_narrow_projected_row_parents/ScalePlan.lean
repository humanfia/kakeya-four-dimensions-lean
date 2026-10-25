import Submission.Obl.k4_narrow_projected_row_parents.WitnessExponent

namespace Submission.Obl.k4_narrow_projected_row_parents

noncomputable section

/-- The coefficient bounds in the scale selection are linear in the starting depth. -/
def parentDepthBound (ℓ L : ℝ) : ℝ := 2 + L / ℓ

def widthExponentBound (ℓ L : ℝ) : ℝ := 2 * ℓ + L

def rowMeshBound (ℓ C L : ℝ) : ℝ :=
  C * (parentDepthBound ℓ L + widthExponentBound ℓ L + L + 3)

/-- Enough room for both the palette mesh and the true depth of the row labels. -/
def narrowLambda (S κ ℓ C L : ℝ) : ℝ :=
  max ((L + 2) / S)
    (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ + 1)

theorem narrowLambda_palette {S κ ℓ C L : ℝ} (hS : 0 < S) :
    L + 2 ≤ S * narrowLambda S κ ℓ C L := by
  have h := (div_le_iff₀ hS).mp (le_max_left ((L + 2) / S)
    (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ + 1))
  simpa only [narrowLambda, mul_comm] using h

/-- The scales required by the list comparison and by the deep-row construction. -/
structure NarrowScales (κ ℓ C L a s B U : ℝ) where
  r : ℝ
  deep : ℝ
  e : ℝ
  mesh : ℝ
  projected_lt : s < r
  deep_lt : r < deep
  below : deep < U
  room : r + mesh / κ + e / ℓ < U
  transverse_gap : ℓ * r < B
  spatial_gap : B < (κ + ℓ) * r
  error_eq : e = (B - ℓ * r) / 8
  mesh_eq : mesh = C * (r + B + (L + 1) * a + s)
  error_pos : 0 < e
  error_mesh : e < mesh
  mesh_slope : e + ℓ * r < mesh
  mesh_major : mesh < κ * (deep - r)
  error_minor : e < ℓ * (deep - r)

theorem exists_narrow_scales {S κ ℓ C L a s B U : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hC : 2 ≤ C) (hL : 2 < L)
    (ha : 0 < a) (has : a ≤ s) (hs2 : s ≤ 2 * a)
    (hB : ℓ * s < B) (hBA : B ≤ ℓ * s + L * a)
    (hU : narrowLambda S κ ℓ C L * a < U) :
    Nonempty (NarrowScales κ ℓ C L a s B U) := by
  have hs : 0 < s := ha.trans_le has
  have hBpos : 0 < B := (mul_pos hℓ hs).trans hB
  have hCpos : 0 < C := by linarith
  obtain ⟨r, hsr, hBr, hspatial, hrB⟩ := exists_true_depth hκ hℓ hs hB
  have hr : 0 < r := hs.trans hsr
  have hBD : B ≤ widthExponentBound ℓ L * a := by
    dsimp [widthExponentBound]
    nlinarith
  have hrD : r ≤ parentDepthBound ℓ L * a := by
    apply hrB.le.trans
    apply (div_le_iff₀ hℓ).mpr
    dsimp [parentDepthBound]
    have hid : ((2 + L / ℓ) * a) * ℓ = (2 * ℓ + L) * a := by field_simp
    rw [hid]
    exact hBD
  let e : ℝ := (B - ℓ * r) / 8
  let mesh : ℝ := C * (r + B + (L + 1) * a + s)
  have he : 0 < e := by dsimp [e]; linarith
  have heB : e ≤ B := by dsimp [e]; nlinarith
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hmeshD : mesh ≤ rowMeshBound ℓ C L * a := by
    calc mesh ≤ C * (parentDepthBound ℓ L * a + widthExponentBound ℓ L * a +
        (L + 1) * a + 2 * a) := by dsimp [mesh]; gcongr
      _ = rowMeshBound ℓ C L * a := by unfold rowMeshBound; ring
  have hmeshSlope : e + ℓ * r < mesh := by
    have hleft : e + ℓ * r < B := by dsimp [e]; linarith
    have hBmesh : B < mesh := by
      dsimp [mesh]
      have hrest : 0 < r + (L + 1) * a + s := by positivity
      nlinarith
    exact hleft.trans hBmesh
  have hroom : r + mesh / κ + e / ℓ < U := by
    have hpre : r + mesh / κ + e / ℓ ≤
        (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ) * a := by
      have hm := div_le_div_of_nonneg_right hmeshD hκ.le
      have he' := div_le_div_of_nonneg_right (heB.trans hBD) hℓ.le
      have hid : (parentDepthBound ℓ L * a) + (rowMeshBound ℓ C L * a) / κ +
          (widthExponentBound ℓ L * a) / ℓ =
          (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ) * a := by ring
      linarith
    have hnext : (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ) * a <
        narrowLambda S κ ℓ C L * a := by
      have hmax := le_max_right ((L + 2) / S)
        (parentDepthBound ℓ L + rowMeshBound ℓ C L / κ + widthExponentBound ℓ L / ℓ + 1)
      apply mul_lt_mul_of_pos_right _ ha
      dsimp [narrowLambda]
      linarith
    exact hpre.trans_lt (hnext.trans hU)
  obtain ⟨r', hrr', hr'U, hmajor, hminor⟩ := exists_deeper_true_depth hκ hℓ he hmesh hroom
  exact ⟨{
    r := r
    deep := r'
    e := e
    mesh := mesh
    projected_lt := hsr
    deep_lt := hrr'
    below := hr'U
    room := hroom
    transverse_gap := hBr
    spatial_gap := hspatial
    error_eq := rfl
    mesh_eq := rfl
    error_pos := he
    error_mesh := by nlinarith
    mesh_slope := hmeshSlope
    mesh_major := hmajor
    error_minor := hminor }⟩

end

end Submission.Obl.k4_narrow_projected_row_parents
