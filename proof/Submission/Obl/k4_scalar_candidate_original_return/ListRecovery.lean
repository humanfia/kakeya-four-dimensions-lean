import Submission.Obl.k4_scalar_candidate_original_return.ObservationTransfer
import Submission.Obl.k4_original_observation_atlas_encoding.Recovery
import Submission.Obl.k4_native_base_flattening.AveragingBridge

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

noncomputable section

def observationCorner (ρ : ℝ) (c : Fin 3 → ℤ) : Base × ℤ :=
  (![ρ * (c 0 : ℝ), ρ * (c 1 : ℝ)], c 2)

lemma observationMeshTag_corner {ρ : ℝ} (hρ : 0 < ρ) (c : Fin 3 → ℤ) :
    observationMeshTag ρ (observationCorner ρ c) = c := by
  funext i
  fin_cases i <;> simp [observationMeshTag, observationCorner, hρ.ne']

lemma scalarMarginal_same_tag (δ ρ : ℝ) {f : (Fin 6 → ℝ) → ℝ}
    (hcell : ∀ w w', (∀ i ∉ ([0, 1] : List (Fin 6)), w i = w' i) →
      (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊w i / ρ⌋ = ⌊w' i / ρ⌋) → f w = f w')
    (z z' : Base × ℤ) (hz : observationMeshTag ρ z = observationMeshTag ρ z') :
    scalarMarginal δ f z = scalarMarginal δ f z' := by
  have h0 : ⌊z.1 0 / ρ⌋ = ⌊z'.1 0 / ρ⌋ := congrFun hz 0
  have h1 : ⌊z.1 1 / ρ⌋ = ⌊z'.1 1 / ρ⌋ := congrFun hz 1
  have h2 : z.2 = z'.2 := congrFun hz 2
  calc
    _ = scalarMarginal δ f (z'.1, z.2) :=
      scalarMarginal_same_cell δ ρ hcell z.1 z'.1 (by
        intro i
        fin_cases i
        · exact h0
        · exact h1) z.2
    _ = _ := by rw [h2]

/-- Maximizing a finite list on the base-cell/original-hidden-bin record
preserves original unnormalized success up to twice the raw density error. -/
theorem recover_original_scalar_lists {W m : ℕ}
    (ω : Fin W → ℝ) (hω : ∀ g, 0 ≤ ω g) (hωsum : ∑ g, ω g = 1)
    (γ : Fin m → Fin W) (δ ρ : ℝ) (hρ : 0 < ρ)
    (μ : Fin m → Measure Inc) (C : Fin m → Set Inc)
    (f g : Fin m → (Fin 6 → ℝ) → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfi : ∀ i, Integrable (f i) volume)
    (hf0 : ∀ i w, 0 ≤ f i w) (hg0 : ∀ i w, 0 ≤ g i w)
    (hsource : ∀ i, ((μ i).restrict (C i)).map fullSourceCoordinates =
      volume.withDensity (fun w => ENNReal.ofReal (f i w)))
    (hcell : ∀ i w w', (∀ j ∉ ([0, 1] : List (Fin 6)), w j = w' j) →
      (∀ j ∈ ([0, 1] : List (Fin 6)), ⌊w j / ρ⌋ = ⌊w' j / ρ⌋) → g i w = g i w')
    (D : ℕ) (L : Fin W → (Base × ℤ) → Finset (Fin m))
    (hLmeas : ∀ a i, MeasurableSet {z | i ∈ L a z})
    (hLcard : ∀ a z, (L a z).card ≤ D) :
    ∃ table : Fin W → (Fin 3 → ℤ) → Finset (Fin m),
      (∀ a c, (table a c).card ≤ D) ∧
      (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
        {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)}) ≤
      (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
        {q | q ∈ C i ∧ i ∈ table (γ i) (observationMeshTag ρ (originalObservation δ q))}) +
        2 * ∑ i, densityL1Distance volume (g i) (f i) := by
  classical
  let reference := (volume : Measure Base).prod (Measure.count : Measure ℤ)
  let p : Fin m → (Base × ℤ) → ℝ≥0∞ := fun i z => ENNReal.ofReal (scalarMarginal δ (f i) z)
  let q : Fin m → (Base × ℤ) → ℝ≥0∞ := fun i z => ENNReal.ofReal (scalarMarginal δ (g i) z)
  have hp (i) : Measurable (p i) := ENNReal.measurable_ofReal.comp (scalarMarginal_measurable δ (hf i))
  have hq (i) : Measurable (q i) := ENNReal.measurable_ofReal.comp (scalarMarginal_measurable δ (hg i))
  have hsum : ∑ a, ENNReal.ofReal (ω a) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hω a), hωsum]
    norm_num
  obtain ⟨table, htable, hsuccess⟩ :=
    k4_original_observation_atlas_encoding.recover_world_lists reference p q hp hq
      (fun a => ENNReal.ofReal (ω a)) hsum γ (observationMeshTag ρ)
      (measurable_observationMeshTag ρ) (observationCorner ρ) (observationMeshTag_corner hρ)
      (fun i z z' hz => congrArg ENNReal.ofReal (scalarMarginal_same_tag δ ρ (hcell i) z z' hz))
      D L hLmeas hLcard
  have htableMeas (a : Fin W) (i : Fin m) :
      MeasurableSet {z | i ∈ table a (observationMeshTag ρ z)} :=
    (measurable_observationMeshTag ρ) ((Set.to_countable {c | i ∈ table a c}).measurableSet)
  have herror (i : Fin m) :
      (∫⁻ z, ((p i z - q i z) + (q i z - p i z)) ∂reference) ≤
        densityL1Distance volume (g i) (f i) := by
    change (∫⁻ z, k4_native_base_flattening.ediff (p i z) (q i z) ∂reference) ≤ _
    simp_rw [p, q, k4_native_base_flattening.ediff_ofReal _ _
      (scalarMarginal_nonneg δ (hf0 i) _) (scalarMarginal_nonneg δ (hg0 i) _)]
    simpa only [densityL1Distance, abs_sub_comm] using scalarMarginal_error δ (hf i) (hg i)
  have hleft : (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
      {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)}) =
      ∑ i, ENNReal.ofReal (ω (γ i)) *
        ∫⁻ z, {z | i ∈ L (γ i) z}.indicator (p i) z ∂reference := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (ω (γ i)) * a)
      (original_observation_mass δ (μ i) (C i) (hf i) (hfi i) (hf0 i) (hsource i) _ (hLmeas _ _))
  have hright : (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
      {q | q ∈ C i ∧ i ∈ table (γ i) (observationMeshTag ρ (originalObservation δ q))}) =
      ∑ i, ENNReal.ofReal (ω (γ i)) *
        ∫⁻ z, {z | i ∈ table (γ i) (observationMeshTag ρ z)}.indicator (p i) z ∂reference := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (ω (γ i)) * a)
      (original_observation_mass δ (μ i) (C i) (hf i) (hfi i) (hf0 i) (hsource i) _ (htableMeas _ _))
  refine ⟨table, htable, ?_⟩
  rw [hleft, hright]
  exact hsuccess.trans (add_le_add le_rfl
    (mul_le_mul_right (Finset.sum_le_sum (fun i _ => herror i)) 2))

end

end Submission.Obl.k4_scalar_candidate_original_return
