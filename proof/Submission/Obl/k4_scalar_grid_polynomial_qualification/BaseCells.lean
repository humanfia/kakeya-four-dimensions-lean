import Submission.Obl.k4_scalar_grid_polynomial_qualification.PlanarLines
import Submission.Obl.k4_scalar_grid_polynomial_qualification.GraphSelection
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalRows
import Submission.Lib.K4ContinuousKakeya.Incidence
set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal ENNReal
open Submission.Lib.K4CommonLocalChoice
namespace Submission.Obl.k4_scalar_grid_polynomial_qualification
noncomputable section

def baseSquare (p : ℝ) (q : Fin 2 → ℤ) : Set BaseLine.Plane :=
  WithLp.ofLp ⁻¹' (univ.pi fun e => Ico ((q e : ℝ) * p) (((q e : ℝ) + 1) * p))

theorem measurableSet_baseSquare (p : ℝ) (q : Fin 2 → ℤ) : MeasurableSet (baseSquare p q) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).preimage (WithLp.measurable_ofLp 2 _)

theorem volume_baseSquare (p : ℝ) (q : Fin 2 → ℤ) : volume (baseSquare p q) = ENNReal.ofReal p ^ 2 := by
  rw [baseSquare, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet, Real.volume_pi_Ico]
  simp only [Fin.prod_univ_two, show ∀ e : Fin 2, ((q e : ℝ) + 1) * p - (q e : ℝ) * p = p by intro e; ring]
  ring

theorem mem_baseSquare_iff {p : ℝ} (hp : 0 < p) (q : Fin 2 → ℤ) (x : BaseLine.Plane) :
    x ∈ baseSquare p q ↔ cell p (WithLp.ofLp x) = q := by
  simp only [baseSquare, mem_preimage, mem_pi, mem_univ, true_implies]
  constructor
  · intro hx
    funext e
    exact Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hp).mpr (hx e).1, (div_lt_iff₀ hp).mpr (hx e).2⟩
  · intro hx e
    have he := Int.floor_eq_iff.mp (congrFun hx e)
    exact ⟨(le_div_iff₀ hp).mp he.1, (div_lt_iff₀ hp).mp he.2⟩

theorem pairwiseDisjoint_baseSquare {p : ℝ} (hp : 0 < p) :
    (univ : Set (Fin 2 → ℤ)).PairwiseDisjoint (baseSquare p) := by
  intro q _ q' _ hqq'
  apply disjoint_left.mpr
  intro x hx hx'
  exact hqq' (((mem_baseSquare_iff hp q x).mp hx).symm.trans ((mem_baseSquare_iff hp q' x).mp hx'))

theorem norm_plane_le_two {z : BaseLine.Plane} {r : ℝ} (hr : 0 ≤ r)
    (hz : ∀ i, |WithLp.ofLp z i| ≤ r) : ‖z‖ ≤ 2 * r := by
  have hsq := EuclideanSpace.norm_sq_eq z
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hsq
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  nlinarith [norm_nonneg z, sq_nonneg (WithLp.ofLp z 0 + r), sq_nonneg (WithLp.ofLp z 0 - r),
    sq_nonneg (WithLp.ofLp z 1 + r), sq_nonneg (WithLp.ofLp z 1 - r)]

def basePart (z : Fin 3 → ℝ) : BaseLine.Plane :=
  WithLp.toLp 2 (fun i : Fin 2 => z i.castSucc)

def baseObservation (b : ℝ) (z : ScalarIncidence) : BaseLine.Plane :=
  basePart (leftCorner b (cell b (scalarPosition z)))

theorem measurable_baseObservation (b : ℝ) : Measurable (baseObservation b) :=
  (measurable_of_countable (fun w : Fin 3 → ℤ => basePart (leftCorner b w))).comp
    (measurable_cell b measurable_scalarPosition)

theorem basePart_scalarPosition (l : ScalarLine) (t : ℝ) :
    basePart (scalarPosition (l, t)) = BaseLine.point l t := by
  ext i
  fin_cases i <;> rfl

theorem norm_basePart_sub_le (z z' : Fin 3 → ℝ) :
    ‖basePart z - basePart z'‖ ≤ 2 * ‖z - z'‖ :=
  norm_plane_le_two (norm_nonneg _) (fun i => norm_le_pi_norm (z - z') i.castSucc)

theorem baseObservation_error {b : ℝ} (hb : 0 < b) (l : ScalarLine) (t : ℝ) :
    dist (baseObservation b (l, t)) (BaseLine.point l t) ≤ 2 * b := by
  rw [dist_eq_norm, ← basePart_scalarPosition, baseObservation]
  exact (norm_basePart_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [norm_sub_rev] using norm_sub_leftCorner_le hb (scalarPosition (l, t)))
      (by norm_num))

theorem baseSquare_distance {p : ℝ} (hp : 0 < p) (q : Fin 2 → ℤ)
    {x y : BaseLine.Plane} (hx : x ∈ baseSquare p q) (hy : y ∈ baseSquare p q) :
    dist x y ≤ 2 * p := by
  have hxy : ‖WithLp.ofLp x - WithLp.ofLp y‖ ≤ p :=
    (norm_sub_lt_of_cell_eq hp
      (((mem_baseSquare_iff hp q x).mp hx).trans ((mem_baseSquare_iff hp q y).mp hy).symm)).le
  rw [dist_eq_norm]
  apply norm_plane_le_two hp.le
  intro i
  exact (norm_le_pi_norm (WithLp.ofLp x - WithLp.ofLp y) i).trans hxy

/-- Every point of an assigned base square lies in a uniform tube around
the actual original affine base trajectory. -/
theorem baseSquare_subset_tube {p b : ℝ} (hp : 0 < p) (hb : 0 < b) (hbp : b ≤ p)
    (l : ScalarLine) (t : ℝ) (q : Fin 2 → ℤ)
    (hobs : baseObservation b (l, t) ∈ baseSquare p q) :
    baseSquare p q ⊆ Submission.Lib.K4ContinuousKakeya.tube (5 * p)
      (BaseLine.intercept l) (BaseLine.direction (l.2 1)) := by
  intro x hx
  apply Metric.mem_thickening_iff.mpr
  refine ⟨BaseLine.point l t, ?_, ?_⟩
  · exact ⟨t * ‖BaseLine.raw (l.2 1)‖, (BaseLine.point_on_line l t).symm⟩
  · have h := (dist_triangle x (baseObservation b (l, t)) (BaseLine.point l t)).trans
      (add_le_add (baseSquare_distance hp q hx hobs) (baseObservation_error hb l t))
    linarith

theorem baseObservation_time_error {b : ℝ} (hb : 0 < b) (z : ScalarIncidence) :
    |(baseObservation b z).ofLp 0 - z.2| ≤ b := by
  have h := (norm_le_pi_norm
    (scalarPosition z - leftCorner b (cell b (scalarPosition z))) 0).trans
      (norm_sub_leftCorner_le hb (scalarPosition z))
  change |leftCorner b (cell b (scalarPosition z)) 0 - z.2| ≤ b
  rw [abs_sub_comm]
  exact h

/-- Assignment through fine-state centers enlarges the time section of one
base square only by the two fine errors. -/
theorem baseSquare_time_section {p b : ℝ} (_hp : 0 < p) (hb : 0 < b)
    (l : ScalarLine) (q : Fin 2 → ℤ) :
    volume {t | baseObservation b (l, t) ∈ baseSquare p q} ≤ ENNReal.ofReal (p + 2 * b) := by
  have hsub : {t | baseObservation b (l, t) ∈ baseSquare p q} ⊆
      Icc ((q 0 : ℝ) * p - b) (((q 0 : ℝ) + 1) * p + b) := by
    intro t ht
    have hsq : (baseObservation b (l, t)).ofLp 0 ∈
        Ico ((q 0 : ℝ) * p) (((q 0 : ℝ) + 1) * p) := ht 0 (mem_univ _)
    have herr := abs_le.mp (baseObservation_time_error hb (l, t))
    exact ⟨by linarith [hsq.1], by linarith [hsq.2]⟩
  calc
    _ ≤ volume (Icc ((q 0 : ℝ) * p - b) (((q 0 : ℝ) + 1) * p + b)) := measure_mono hsub
    _ = _ := by rw [Real.volume_Icc]; congr 1; ring

/-- The existing incidence Kakeya projection lemma applies to the actual
fine-center base squares with the original trajectory prior. -/
theorem baseSquare_pushforward_cap (θ : Measure ScalarLine) [SFinite θ]
    (inc : Measure ScalarIncidence) (K : ℝ≥0) (hinc : inc ≤ K • θ.prod volume)
    {p b : ℝ} (hp : 0 < p) (hb : 0 < b)
    (Λ : Set ScalarLine) (hΛ : MeasurableSet Λ) (q : Fin 2 → ℤ) :
    (inc.restrict {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q}).map Prod.fst ≤
      (K * Real.toNNReal (p + 2 * b)) • θ.restrict Λ := by
  apply Submission.Lib.K4ContinuousKakeya.map_fst_restrict_le θ inc K _ hinc _
    ((measurable_fst hΛ).inter ((measurable_baseObservation b) (measurableSet_baseSquare p q)))
    Λ hΛ (fun _ hz => hz.1)
  intro l _
  calc
    _ ≤ volume {t | baseObservation b (l, t) ∈ baseSquare p q} := measure_mono (fun _ ht => ht.2)
    _ ≤ ENNReal.ofReal (p + 2 * b) := baseSquare_time_section hp hb l q
    _ = _ := rfl

/-- Every occupied base code is the projection of an occupied physical
code. This converts planar filling to the physical counts used below. -/
theorem base_cell_card_le_of_physical_cover {X : Type*} (Z : X → Fin 3 → ℝ)
    (E : Set X) (p : ℝ) (F : Finset (Fin 3 → ℤ)) (B : Finset (Fin 2 → ℤ))
    (hF : ∀ z ∈ E, cell p (Z z) ∈ F)
    (hB : ∀ q ∈ B, ∃ z ∈ E, cell p (fun e : Fin 2 => Z z e.castSucc) = q) :
    B.card ≤ F.card := by
  classical
  let project : (Fin 3 → ℤ) → Fin 2 → ℤ := fun c e => c e.castSucc
  have hsub : B ⊆ F.image project := by
    intro q hq
    obtain ⟨z, hz, hzq⟩ := hB q hq
    exact Finset.mem_image.mpr ⟨cell p (Z z), hF z hz, hzq⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
end
end Submission.Obl.k4_scalar_grid_polynomial_qualification
