/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ComparisonCoordinates.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.HorizontalFlow
import Submission.Lib.K4AffineMeshCaps.Transport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Normalize one time block and one unchanged static parameter square. -/
def normalizeStatic (t₀ H p₀ q₀ D : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(z 0 - t₀) / H, (z 1 - p₀) / D, (z 2 - q₀) / D]

/-- Physical base coordinates are first returned to the determinant-one reference flow. -/
def comparisonCoordinates (v t₀ H p₀ q₀ D : ℝ) (z : Fin 3 → ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (normalizeStatic t₀ H p₀ q₀ D (reconstructBase v z))

theorem measurable_normalizeStatic (t₀ H p₀ q₀ D : ℝ) :
    Measurable (normalizeStatic t₀ H p₀ q₀ D) := by
  unfold normalizeStatic
  fun_prop

theorem measurable_comparisonCoordinates (v t₀ H p₀ q₀ D : ℝ) :
    Measurable (comparisonCoordinates v t₀ H p₀ q₀ D) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
    ((measurable_normalizeStatic _ _ _ _ _).comp (horizontalFlowEquiv v).symm.measurable)

theorem map_normalizeStatic_volume (t₀ p₀ q₀ : ℝ) {H D : ℝ}
    (hH : 0 < H) (hD : 0 < D) :
    Measure.map (normalizeStatic t₀ H p₀ q₀ D) (volume : Measure (Fin 3 → ℝ)) =
      ENNReal.ofReal (H * D ^ 2) • volume := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![H⁻¹, D⁻¹, D⁻¹]
  let c : Fin 3 → ℝ := ![-t₀ / H, -p₀ / D, -q₀ / D]
  have hdet : M.det = (H * D ^ 2)⁻¹ := by
    simp [M, Matrix.det_diagonal, Fin.prod_univ_three, pow_two]
    ring
  have hM : M.det ≠ 0 := by rw [hdet]; positivity
  have hf : normalizeStatic t₀ H p₀ q₀ D = affineBase M c := by
    funext z
    ext i
    fin_cases i <;> simp [normalizeStatic, affineBase, M, c, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, div_eq_mul_inv] <;> ring
  rw [hf, map_affineBase_volume M c hM, hdet,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < H * D ^ 2)), inv_inv]

/-- The exact normalization Jacobian includes the determinant-one horizontal motion
and the Pi-to-Euclidean volume conversion required by the graph matching theorem. -/
theorem map_comparisonCoordinates_volume (v t₀ p₀ q₀ : ℝ) {H D : ℝ}
    (hH : 0 < H) (hD : 0 < D) :
    Measure.map (comparisonCoordinates v t₀ H p₀ q₀ D)
      (volume : Measure (Fin 3 → ℝ)) =
        ENNReal.ofReal (H * D ^ 2) • volume := by
  have hLp : Measurable (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable
  have hr : Measurable (reconstructBase v) := (horizontalFlowEquiv v).symm.measurable
  have hn := measurable_normalizeStatic t₀ H p₀ q₀ D
  change Measure.map ((WithLp.toLp 2) ∘
    ((normalizeStatic t₀ H p₀ q₀ D) ∘ (reconstructBase v))) volume = _
  rw [← Measure.map_map hLp (hn.comp hr), ← Measure.map_map hn hr,
    (measurePreserving_reconstructBase v).map_eq,
    map_normalizeStatic_volume t₀ p₀ q₀ hH hD,
    Measure.map_smul _ hLp.aemeasurable,
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq]


/-- A continuous physical density ceiling transports with the original factor `H D²`.
Neither the current incidence law nor a trajectory prior is renormalized. -/
theorem comparisonCoordinates_density (μ : Measure (Fin 3 → ℝ)) (C : ENNReal)
    (hμ : μ ≤ C • volume) (v t₀ p₀ q₀ : ℝ) {H D : ℝ}
    (hH : 0 < H) (hD : 0 < D) :
    μ.map (comparisonCoordinates v t₀ H p₀ q₀ D) ≤
      (C * ENNReal.ofReal (H * D ^ 2)) • volume := by
  have hb := Measure.map_mono hμ (measurable_comparisonCoordinates v t₀ H p₀ q₀ D)
  rw [Measure.map_smul _ (measurable_comparisonCoordinates v t₀ H p₀ q₀ D).aemeasurable,
    map_comparisonCoordinates_volume v t₀ p₀ q₀ hH hD, smul_smul] at hb
  exact hb

/-- A padded normalization puts the entire original product domain in the
real half ball used by the matching theorem. -/
theorem norm_fin3_le_half {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ∀ i, |x i| ≤ (1 : ℝ) / 4) : ‖x‖ ≤ 1 / 2 := by
  have hs (i : Fin 3) : (x i) ^ 2 ≤ 1 / 16 := by
    have hh := abs_le.mp (hx i)
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ (1 : ℝ) / 4 + x i)]
  have heq := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_three] at heq
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg x]

theorem comparisonCoordinates_mem_half {v t₀ H p₀ q₀ D : ℝ} {z : Fin 3 → ℝ}
    (hH : 0 < H) (hD : 0 < D)
    (ht : |z 0 - t₀| ≤ H / 4) (hp : |reconstructBase v z 1 - p₀| ≤ D / 4)
    (hq : |reconstructBase v z 2 - q₀| ≤ D / 4) :
    ‖comparisonCoordinates v t₀ H p₀ q₀ D z‖ ≤ 1 / 2 := by
  apply norm_fin3_le_half
  intro i
  fin_cases i
  · change |(z 0 - t₀) / H| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hH, div_le_iff₀ hH]
    linarith
  · change |(reconstructBase v z 1 - p₀) / D| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    linarith
  · change |(reconstructBase v z 2 - q₀) / D| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    linarith

end

end Submission.Obl.k4_horizontal_strict_parameter_step
