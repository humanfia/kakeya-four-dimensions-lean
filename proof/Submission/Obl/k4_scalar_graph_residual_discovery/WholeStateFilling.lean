/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WholeStateFilling.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.StripFillingFromBreadth
import Submission.Obl.k4_scalar_graph_residual_discovery.FiniteRecords
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldStripSupport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Metric
open scoped ENNReal NNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- Planar filling for an ACTUAL global union of original fine states.
The independent breadth comes from the final global law; a long-entry
prior bound may refer to an earlier law. This proves physical filling,
without restricting to a coefficient world. -/
theorem whole_state_planar_filling
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ]
    {R : Set ScalarIncidence} (hR : MeasurableSet R)
    {b p ρ H K C vsep L : ℝ} (hb : 0 < b) (hp : 0 < p) (hbp : b ≤ p) (hp₁ : p ≤ 1)
    (hρ : 0 < ρ) (hH : 1 ≤ H) (hK : 0 < K) (hC : 0 ≤ C) (hMK : FiniteMK 2 C)
    (hvsep : 0 < vsep) (hL : 0 < L) (U : ℝ≥0) (hU : 3 * (U : ℝ) ≤ K)
    (hdom : μ.restrict R ≤ U • θ.prod volume)
    (hcoeff : ∀ z ∈ R, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ R, z.2 ∈ Icc (0 : ℝ) 1)
    (hfinite : ((fun z => cell b (scalarPosition z)) '' R).Finite)
    (hstates : ∀ S : Set (Fin 3 → ℤ), ∀ w : ℝ,
      ((μ.restrict R).restrict ((fun z => cell b (scalarPosition z)) ⁻¹' S))
        {z | |z.1.2 1 - w| ≤ vsep} ≤
          (1 / 2 : ℝ≥0∞) * (μ.restrict R) ((fun z => cell b (scalarPosition z)) ⁻¹' S))
    (S : Set (Fin 3 → ℤ))
    (Λ : Set ScalarLine) (hΛ : MeasurableSet Λ) (hΛbound : ∀ l ∈ Λ, |l.2 0| ≤ H)
    (hΛpoint : ∀ z ∈ R, cell b (scalarPosition z) ∈ S → z.1 ∈ Λ)
    (hpositive : μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≠ 0)
    (hprior : (θ Λ).toReal ≤
      K * (μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S)).toReal / ρ)
    (hbudget : 200 * C * K ^ 4 * (1 + H) ^ 2 ≤ L * vsep) :
    (ρ / p) ^ 2 / L ≤
      (((fun z => cell p (assignedPosition b z)) ''
        (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S)).ncard : ℝ) := by
  classical
  let state (z : ScalarIncidence) := cell b (scalarPosition z)
  have hstate : Measurable state := measurable_cell b measurable_scalarPosition
  let E := R ∩ state ⁻¹' S
  have hE : MeasurableSet E := hR.inter (hstate (to_countable S).measurableSet)
  let κ := μ.restrict R
  let inc := μ.restrict E
  have hinc : inc ≤ U • θ.prod volume :=
    (Measure.restrict_mono_set μ inter_subset_left).trans hdom
  have hphysfinite : ((fun z => cell p (assignedPosition b z)) '' E).Finite := by
    apply (hfinite.image (fun w => cell p (leftCorner b w))).subset
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨state z, ⟨z, hz.1, rfl⟩, rfl⟩
  let P := hphysfinite.toFinset
  let project (w : Fin 3 → ℤ) (e : Fin 2) := w e.castSucc
  let B := P.image project
  have hproject (z : ScalarIncidence) :
      project (cell p (assignedPosition b z)) = cell p (WithLp.ofLp (baseObservation b z)) := by
    ext e
    rfl
  have hbase (z : ScalarIncidence) (hz : z ∈ E) :
      cell p (WithLp.ofLp (baseObservation b z)) ∈ B := by
    rw [← hproject]
    exact Finset.mem_image.mpr ⟨cell p (assignedPosition b z),
      hphysfinite.mem_toFinset.mpr ⟨z, hz, rfl⟩, rfl⟩
  have hBocc (q : Fin 2 → ℤ) (hq : q ∈ B) :
      ∃ z ∈ E, baseObservation b z ∈ baseSquare p q := by
    obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz, hzw⟩ := hphysfinite.mem_toFinset.mp hw
    change cell p (assignedPosition b z) = w at hzw
    refine ⟨z, hz, (mem_baseSquare_iff hp q _).mpr ?_⟩
    rw [← hproject, hzw, hwq]
  have hobs (z : ScalarIncidence) (hz : z ∈ E) : ‖baseObservation b z‖ ≤ 2 * (3 * H + b) := by
    have ht : |z.2| ≤ 1 := by rw [abs_of_nonneg (htime z hz.1).1]; exact (htime z hz.1).2
    have hactual := scalarPosition_abs_le_three hH z.1 (hcoeff z hz.1) ht
    apply norm_plane_le_two (by positivity : 0 ≤ 3 * H + b)
    intro e
    have herr := (norm_le_pi_norm (leftCorner b (state z) - scalarPosition z) e.castSucc).trans
      (by simpa only [state, norm_sub_rev] using norm_sub_leftCorner_le hb (scalarPosition z))
    change |leftCorner b (state z) e.castSucc| ≤ 3 * H + b
    have ha := abs_le.mp (hactual e.castSucc)
    have he := abs_le.mp herr
    simp only [Pi.sub_apply, scalarPosition] at ha he
    apply abs_le.mpr
    constructor <;> linarith
  have hER (q : Fin 2 → ℤ) (hq : q ∈ B) : baseSquare p q ⊆ closedBall 0 (6 * H + 4) := by
    obtain ⟨z, hz, hobsq⟩ := hBocc q hq
    intro x hx
    apply mem_closedBall.mpr
    calc
      dist x 0 ≤ dist x (baseObservation b z) + dist (baseObservation b z) 0 := dist_triangle _ _ _
      _ ≤ 2 * p + 2 * (3 * H + b) := add_le_add
        (baseSquare_distance hp q hx hobsq) (by simpa only [dist_zero_right] using hobs z hz)
      _ ≤ _ := by linarith
  have hcover : ∀ᵐ z ∂inc, ∃ q ∈ B, z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q := by
    filter_upwards [ae_restrict_mem hE] with z hz
    refine ⟨cell p (WithLp.ofLp (baseObservation b z)), hbase z hz, hΛpoint z hz.1 hz.2, ?_⟩
    exact (mem_baseSquare_iff hp _ _).mpr rfl
  have hvel : ∀ᵐ z ∂inc, |z.1.2 1| ≤ H := by
    filter_upwards [ae_restrict_mem hE] with z hz
    exact hcoeff z hz.1 1
  have hcap (q : Fin 2 → ℤ) (_ : q ∈ B) (w : ℝ) :
      (inc.restrict {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q})
        {z | |z.1.2 1 - w| ≤ vsep} ≤
          (1 / 2 : ℝ≥0∞) * inc {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q} := by
    let T := S ∩ {u | basePart (leftCorner b u) ∈ baseSquare p q}
    let A := {z : ScalarIncidence | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q}
    have hT : MeasurableSet (state ⁻¹' T) := hstate (to_countable T).measurableSet
    have hA : MeasurableSet A := (hΛ.preimage measurable_fst).inter
      ((measurable_baseObservation b) (measurableSet_baseSquare p q))
    have hsets : A ∩ E = (state ⁻¹' T) ∩ R := by
      ext z
      change ((z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q) ∧ z ∈ R ∧ state z ∈ S) ↔
        ((state z ∈ S ∧ baseObservation b z ∈ baseSquare p q) ∧ z ∈ R)
      constructor
      · rintro ⟨⟨_, hq⟩, hz, hs⟩
        exact ⟨⟨hs, hq⟩, hz⟩
      · rintro ⟨⟨hs, hq⟩, hz⟩
        exact ⟨⟨hΛpoint z hz hs, hq⟩, hz, hs⟩
    have hmeasures : inc.restrict A = κ.restrict (state ⁻¹' T) := by
      dsimp only [inc, κ]
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict hT, hsets]
    have hmass : inc A = κ (state ⁻¹' T) := by
      calc
        _ = (inc.restrict A) univ := by rw [Measure.restrict_apply_univ]
        _ = _ := by rw [hmeasures, Measure.restrict_apply_univ]
    change (inc.restrict A) _ ≤ (1 / 2 : ℝ≥0∞) * inc A
    rw [hmeasures, hmass]
    exact hstates T w
  have hincpositive : inc univ ≠ 0 := by
    simpa only [inc, Measure.restrict_apply_univ] using hpositive
  have hprior' : (θ Λ).toReal ≤ K * (inc univ).toReal / ρ := by
    simpa only [inc, Measure.restrict_apply_univ] using hprior
  have hfill := assigned_strip_filling_of_cell_breadth θ inc hC hMK hK hρ hp hb hbp
    hvsep (by linarith : 0 ≤ H) hL U hU hinc Λ hΛ hΛbound B hER hcover
    hincpositive hprior' hvel hcap hbudget
  have hcard : (B.card : ℝ) ≤ P.card := by exact_mod_cast (Finset.card_image_le : B.card ≤ P.card)
  rw [Set.ncard_eq_toFinset_card _ hphysfinite]
  exact hfill.trans hcard

end

end Submission.Obl.k4_scalar_graph_residual_discovery
