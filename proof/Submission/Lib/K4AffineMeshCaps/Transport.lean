/-
Adapted from: here:o222 (x0774), AffineMeshCap.lean.
-/
import Submission.Lib.K4AffineMeshCaps.Saturation

/-! Finite-mesh caps under arbitrary invertible affine base changes. -/

namespace Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set Matrix

noncomputable section

def affineBase (M : Matrix (Fin 3) (Fin 3) ℝ) (b z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  M.mulVec z + b

theorem measurable_affineBase (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) :
    Measurable (affineBase M b) := by
  unfold affineBase Matrix.mulVec dotProduct
  fun_prop

theorem map_affineBase_volume (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (hM : M.det ≠ 0) :
    Measure.map (affineBase M b) volume = ENNReal.ofReal |M.det|⁻¹ • volume := by
  have hfun : affineBase M b = (fun z => z + b) ∘ (Matrix.toLin' M) := by
    funext z
    simp [affineBase, Matrix.toLin'_apply]
  have hlin : Measurable (Matrix.toLin' M) := (LinearMap.continuous_on_pi _).measurable
  rw [hfun, ← Measure.map_map (measurable_add_const b) hlin,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hM,
    Measure.map_smul, map_add_right_eq_self, abs_inv]
  all_goals exact (measurable_add_const b).aemeasurable

theorem volume_affineBase_preimage (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (hM : M.det ≠ 0) (B : Set (Fin 3 → ℝ)) (hB : MeasurableSet B) :
    volume (affineBase M b ⁻¹' B) = ENNReal.ofReal |M.det|⁻¹ * volume B := by
  rw [← Measure.map_apply (measurable_affineBase M b) hB,
    map_affineBase_volume M b hM, Measure.smul_apply, smul_eq_mul]

theorem affineBase_coordinate_variation (M : Matrix (Fin 3) (Fin 3) ℝ)
    (b : Fin 3 → ℝ) {delta : ℝ} {z w : Fin 3 → ℝ}
    (hdist : ∀ j, |z j - w j| ≤ delta) (i : Fin 3) :
    |affineBase M b z i - affineBase M b w i| ≤ ∑ j, |M i j| * delta := by
  have heq : affineBase M b z i - affineBase M b w i =
      ∑ j, M i j * (z j - w j) := by
    simp only [affineBase, Pi.add_apply, Matrix.mulVec, dotProduct, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ ∑ j, |M i j * (z j - w j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |M i j| * |z j - w j| := by simp only [abs_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hdist j) (abs_nonneg _))

/-- Resolving the affine map on a finer source mesh retains its exact
Jacobian, including spatial shears. Any extra original incidence event survives. -/
theorem affine_mesh_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {delta sigma C : ℝ} (hd : 0 < delta) (hs : 0 < sigma) (hC : 0 ≤ C)
    (hresolve : ∀ i, (∑ j, |M i j| * delta) ≤ sigma)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * delta ^ 3))
    (q : Fin 3 → ℤ) :
    μ {p | baseMesh sigma (affineBase M b (Z p)) = q ∧ condition p} ≤
      ENNReal.ofReal (27 * C * |M.det|⁻¹ * sigma ^ 3) := by
  let S : Set (Fin 3 → ℝ) := {z | baseMesh sigma (affineBase M b z) = q}
  let lo : Fin 3 → ℝ := fun i => sigma * ((q i : ℝ) - 1)
  let hi : Fin 3 → ℝ := fun i => sigma * ((q i : ℝ) + 2)
  have hsub : meshSaturation delta S ⊆ affineBase M b ⁻¹' Icc lo hi := by
    intro z hz
    obtain ⟨w, hw, hdist⟩ := meshSaturation_close hd S hz
    have hclose (i : Fin 3) :
        |affineBase M b z i - affineBase M b w i| ≤ sigma :=
      (affineBase_coordinate_variation M b hdist i).trans (hresolve i)
    have hbin (i : Fin 3) := Int.floor_eq_iff.mp (congrFun hw i)
    constructor
    · intro i
      have hh := hbin i
      rw [le_div_iff₀ hs, div_lt_iff₀ hs] at hh
      have hc := abs_le.mp (hclose i)
      dsimp [lo]
      linarith
    · intro i
      have hh := hbin i
      rw [le_div_iff₀ hs, div_lt_iff₀ hs] at hh
      have hc := abs_le.mp (hclose i)
      dsimp [hi]
      linarith
  have hvolume : volume (Icc lo hi) = ENNReal.ofReal (27 * sigma ^ 3) := by
    rw [Real.volume_Icc_pi]
    have hlength (i : Fin 3) : hi i - lo i = 3 * sigma := by dsimp [hi, lo]; ring
    simp_rw [hlength]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i hi => by positivity)]
    simp only [Fin.prod_univ_three]
    congr 1
    ring
  change μ {p | Z p ∈ S ∧ condition p} ≤ _
  calc
    _ ≤ ENNReal.ofReal C * volume (meshSaturation delta S) :=
      measure_le_meshSaturation_volume μ Z condition hd hC hcap S
    _ ≤ ENNReal.ofReal C * volume (affineBase M b ⁻¹' Icc lo hi) := by
      exact mul_le_mul le_rfl (measure_mono hsub) bot_le bot_le
    _ = ENNReal.ofReal C * (ENNReal.ofReal |M.det|⁻¹ * ENNReal.ofReal (27 * sigma ^ 3)) := by
      rw [volume_affineBase_preimage M b hM _ measurableSet_Icc, hvolume]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _)), ← ENNReal.ofReal_mul hC]
      congr 1
      ring

/-- Summing the finitely many bounded signal bins gives a pure base cap,
while keeping any other original incidence condition. -/
theorem base_cell_cap_of_bounded_signal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (signal : Ω → ℝ) (condition : Ω → Prop)
    {delta a L C : ℝ} (hd : 0 < delta) (ha : 0 < a) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbound : ∀ᵐ p ∂μ, condition p → |signal p| ≤ L)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh delta (Z p) = q ∧ ⌊signal p / a⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * delta ^ 3)) (q : Fin 3 → ℤ) :
    μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤
      ENNReal.ofReal ((4 * L / a + 2) * C * delta ^ 3) := by
  classical
  obtain ⟨F, hF, hcover⟩ := interval_mesh_cover ha hL (0 : ℝ)
  have hsub : {p | baseMesh delta (Z p) = q ∧ condition p} ≤ᵐ[μ]
      ⋃ j ∈ F, {p | baseMesh delta (Z p) = q ∧ ⌊signal p / a⌋ = j ∧ condition p} := by
    filter_upwards [hbound] with p hp
    intro he
    exact mem_iUnion.mpr ⟨⌊signal p / a⌋,
      mem_iUnion.mpr ⟨hcover _ (by simpa using hp he.2), he.1, rfl, he.2⟩⟩
  calc
    _ ≤ μ (⋃ j ∈ F, {p | baseMesh delta (Z p) = q ∧ ⌊signal p / a⌋ = j ∧ condition p}) :=
      measure_mono_ae hsub
    _ ≤ ∑ j ∈ F, μ {p | baseMesh delta (Z p) = q ∧ ⌊signal p / a⌋ = j ∧ condition p} :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _j ∈ F, ENNReal.ofReal (C * delta ^ 3) := Finset.sum_le_sum (fun j hj => hcap q j)
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * delta ^ 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (4 * L / a + 2) * (C * delta ^ 3) :=
          mul_le_mul_of_nonneg_right hF (by positivity)
        _ = _ := by ring

end

end Submission.Lib.K4AffineMeshCaps
