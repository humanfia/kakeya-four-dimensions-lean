/- Adapted within this LOT tree from o006/x0006, Submission/Obl/k4_core/FiniteSmoothing/Smoothing.lean.
Original o018/x0048 attribution is retained below. -/

/- Adapted from the same LOT tree, obligation o018, session x0048, commit 6d775765b92912e6ea3c223ec01500dda1f728e5,
Submission/Obl/k4_framework_from_matching_clustering_conic/Smoothing.lean. Namespace and own-submodule import paths changed; proof content retained. -/

import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.UniformBoxes
import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.LineGeometry

/-! The finite-line smoothing step of Theorem 2.17, starting with the graph
coordinates and the separated directions in the frozen DK4 statement. -/

open MeasureTheory Set Metric
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

theorem norm_toLp_sub_le_of_mem_coordBox {r : ℝ} (hr : 0 ≤ r)
    {z c : Fin 3 → ℝ} (hz : z ∈ coordBox r c) :
    ‖WithLp.toLp 2 z - WithLp.toLp 2 c‖ ≤ 3 * r := by
  exact norm_toLp_three_le hr (mem_coordBox_iff.mp hz)

theorem norm_toLp_le_of_mem_coordBox {r : ℝ} (hr : 0 ≤ r)
    {z c : Fin 3 → ℝ} (hz : z ∈ coordBox r c) :
    ‖WithLp.toLp 2 z‖ ≤ ‖WithLp.toLp 2 c‖ + 3 * r := by
  calc
    ‖WithLp.toLp 2 z‖ =
        ‖(WithLp.toLp 2 z - WithLp.toLp 2 c) + WithLp.toLp 2 c‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖WithLp.toLp 2 z - WithLp.toLp 2 c‖ + ‖WithLp.toLp 2 c‖ := norm_add_le _ _
    _ ≤ 3 * r + ‖WithLp.toLp 2 c‖ :=
      add_le_add (norm_toLp_sub_le_of_mem_coordBox hr hz) le_rfl
    _ = ‖WithLp.toLp 2 c‖ + 3 * r := add_comm _ _

theorem smoothedPrior_bounded_support {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x v : Fin n → EuclideanSpace ℝ (Fin 4)) {R M : ℝ}
    (hx : ∀ i, ‖x i‖ ≤ R) (hv : ∀ i, ‖v i‖ ≤ M) :
    smoothedPrior r (fun i => spatialCoords (x i)) (fun i => spatialCoords (v i))
      {p | ‖WithLp.toLp 2 p.1‖ ≤ R + 3 * r ∧
        ‖WithLp.toLp 2 p.2‖ ≤ M + 3 * r}ᶜ = 0 := by
  apply smoothedPrior_support hr
  rintro i ⟨b, s⟩ ⟨hb, hs⟩
  exact ⟨(norm_toLp_le_of_mem_coordBox hr.le hb).trans
      (add_le_add ((norm_spatialCoords_le (x i)).trans (hx i)) le_rfl),
    (norm_toLp_le_of_mem_coordBox hr.le hs).trans
      (add_le_add ((norm_spatialCoords_le (v i)).trans (hv i)) le_rfl)⟩

theorem coordBox_pairwise_disjoint {n : ℕ} {r δ : ℝ}
    (hr : 0 ≤ r) (hgap : 6 * r < δ) (s : Fin n → Fin 3 → ℝ)
    (hs : ∀ i j, i ≠ j → δ ≤ ‖WithLp.toLp 2 (s i) - WithLp.toLp 2 (s j)‖) :
    Pairwise (fun i j => Disjoint (coordBox r (s i)) (coordBox r (s j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  rw [mem_coordBox_iff] at hzi hzj
  have hb (k : Fin 3) : |s i k - s j k| ≤ 2 * r := by
    calc
      |s i k - s j k| = |(s i k - z k) + (z k - s j k)| := by congr 1; ring
      _ ≤ |s i k - z k| + |z k - s j k| := abs_add_le _ _
      _ ≤ r + r := add_le_add (by simpa [abs_sub_comm] using hzi k) (hzj k)
      _ = 2 * r := by ring
  have hn := norm_toLp_three_le (by positivity : 0 ≤ 2 * r) hb
  change ‖WithLp.toLp 2 (s i) - WithLp.toLp 2 (s j)‖ ≤ 3 * (2 * r) at hn
  linarith [hs i j hij]

/-- Incidences lying in a spatial covering set during the common graph-time interval. -/
def selectedIncidences (U : Set (EuclideanSpace ℝ (Fin 4))) :
    Set (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ graphLine p.1.1 p.1.2 p.2 ∈ U}

theorem measurableSet_selectedIncidences {U : Set (EuclideanSpace ℝ (Fin 4))}
    (hU : MeasurableSet U) : MeasurableSet (selectedIncidences U) :=
  (measurableSet_Icc.preimage measurable_snd).inter
    (hU.preimage continuous_graphLine.measurable)

theorem selectedIncidences_subset (U : Set (EuclideanSpace ℝ (Fin 4))) :
    selectedIncidences U ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
  fun _ h => ⟨mem_univ _, h.1⟩

/-- The selected mass is preserved when all balls are enlarged by the perturbation error. -/
theorem smoothedPrior_cover_mass {n m : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (b s : Fin n → Fin 3 → ℝ)
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ) (a : ℝ≥0∞)
    (ha : ∀ i, a ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      graphLine (b i) (s i) t ∈ ⋃ j, ball (z j) (ρ j)}) :
    a ≤ (smoothedPrior r b s).prod volume
      (selectedIncidences (⋃ j, ball (z j) (ρ j + 6 * r))) := by
  apply smoothedPrior_time_mass hn hr b s _ a ha
  rintro i ⟨⟨b', s'⟩, t⟩ ⟨⟨hb, hs⟩, ht, hcov⟩
  refine ⟨ht, ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcov
  exact mem_iUnion.mpr ⟨j, graphLine_perturbation_mem_ball hr.le
    (mem_coordBox_iff.mp hb) (mem_coordBox_iff.mp hs) ht hj⟩

/-- A finite bad DK4 configuration gives an honest probability prior with a bounded full
slope marginal and with the original time-mass floor in a fixed enlargement of its cover.
The coefficient space retains all six independent perturbation coordinates. -/
theorem finite_line_smoothing {n m : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (x v : Fin n → EuclideanSpace ℝ (Fin 4))
    (hx : ∀ i, x i 0 = 0) (hv : ∀ i, v i 0 = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖)
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ)
    (hρ : ∀ j, ρ j ≤ δ) (a : ℝ≥0∞)
    (ha : ∀ i, a ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      x i + t • v i ∈ ⋃ j, ball (z j) (ρ j)}) :
    ∃ ν : Measure ((Fin 3 → ℝ) × (Fin 3 → ℝ)),
      IsProbabilityMeasure ν ∧
      (∀ A : Set (Fin 3 → ℝ), ν (univ ×ˢ A) ≤
        (n : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (δ / 6) ^ 3)⁻¹ * volume A) ∧
      a ≤ (ν.prod volume) (selectedIncidences (⋃ j, ball (z j) (2 * δ))) := by
  let b : Fin n → Fin 3 → ℝ := fun i => spatialCoords (x i)
  let s : Fin n → Fin 3 → ℝ := fun i => spatialCoords (v i)
  have hr : 0 < δ / 12 := by positivity
  have hdisj : Pairwise (fun i j =>
      Disjoint (coordBox (δ / 12) (s i)) (coordBox (δ / 12) (s j))) := by
    apply coordBox_pairwise_disjoint (δ := δ) hr.le (by linarith) s
    intro i j hij
    simpa [s, norm_spatialCoords_sub (hv i) (hv j)] using hsep i j hij
  refine ⟨smoothedPrior (δ / 12) b s,
    smoothedPrior_isProbabilityMeasure hn hr b s, ?_, ?_⟩
  · intro A
    have hrad : 2 * (δ / 12) = δ / 6 := by ring
    simpa only [hrad] using smoothedPrior_slope_le hr b s hdisj A
  · have ha' : ∀ i, a ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        graphLine (b i) (s i) t ∈ ⋃ j, ball (z j) (ρ j)} := by
      intro i
      simpa only [b, s, graphLine_spatialCoords (hx i) (hv i)] using ha i
    apply (smoothedPrior_cover_mass hn hr b s z ρ a ha').trans
    apply measure_mono
    rintro p ⟨ht, hp⟩
    refine ⟨ht, ?_⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    refine mem_iUnion.mpr ⟨j, ball_subset_ball ?_ hj⟩
    linarith [hρ j]

end Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing
