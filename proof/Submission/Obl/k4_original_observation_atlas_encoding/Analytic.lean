import Submission.Obl.k4_original_observation_atlas_encoding.Recovery
import Submission.Obl.k4_original_observation_atlas_encoding.Source
import Submission.Obl.k4_horizon_light_cell_mass.Mesh

namespace Submission.Obl.k4_original_observation_atlas_encoding

open MeasureTheory Set Finset
open scoped ENNReal
open Submission.Obl.k4_horizon_light_cell_mass
open Submission.Obl.k4_native_base_flattening (ediff ediff_ofReal baseCoordinates)
open Submission.Lib.K4ModelReduction (densityL1Distance)

/-- The original incidence laws retain their success when the approximating observation
densities are maximized on the base mesh and the original hidden tag. -/
theorem recover_original_family {W C : ℕ}
    (ω : Fin W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (γ : Fin C → Fin W) (B : Fin W → ℝ) (a ρ : ℝ) (hρ : 0 < ρ)
    (μ : Fin C → Measure State) (F : Fin C → Set State)
    (f g : Fin C → Raw → ℝ) (hf : ∀ b, Measurable (f b)) (hg : ∀ b, Measurable (g b))
    (hf0 : ∀ b x, 0 ≤ f b x) (hg0 : ∀ b x, 0 ≤ g b x)
    (hraw : ∀ b, ((μ b).restrict (F b)).map rawChart =
      volume.withDensity (fun x => ENNReal.ofReal (f b x)))
    (hcell : ∀ b x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g b x = g b y)
    (K : ℕ) (L : Fin W → Observation → Finset (Fin C))
    (hL : ∀ w b, MeasurableSet {o | b ∈ L w o}) (hLK : ∀ w o, (L w o).card ≤ K) :
    ∃ table : Fin W → CellCode → Finset (Fin C), (∀ w c, (table w c).card ≤ K) ∧
      (∑ b, ENNReal.ofReal (ω (γ b)) * (μ b)
        {p | p ∈ F b ∧ b ∈ L (γ b) (pureMap (B (γ b)) a p)}) ≤
      (∑ b, ENNReal.ofReal (ω (γ b)) * (μ b)
        {p | p ∈ F b ∧ b ∈ table (γ b) (meshCode ![ρ, ρ, ρ] (pureMap (B (γ b)) a p))}) +
        2 * ∑ b, densityL1Distance volume (g b) (f b) := by
  classical
  let p : Fin C → Observation → ℝ≥0∞ :=
    fun b => pureMarginal (B (γ b)) a (fun x => ENNReal.ofReal (f b x))
  let q : Fin C → Observation → ℝ≥0∞ :=
    fun b => pureMarginal (B (γ b)) a (fun x => ENNReal.ofReal (g b x))
  have hp (b) : Measurable (p b) :=
    pureMarginal_measurable _ _ (ENNReal.measurable_ofReal.comp (hf b))
  have hq (b) : Measurable (q b) :=
    pureMarginal_measurable _ _ (ENNReal.measurable_ofReal.comp (hg b))
  have hv : ∑ w, ENNReal.ofReal (ω w) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hsum]
    norm_num
  have hqc (b) : ∀ z z', meshCode ![ρ, ρ, ρ] z = meshCode ![ρ, ρ, ρ] z' → q b z = q b z' := by
    apply pureMarginal_same_mesh (B (γ b)) a ρ ρ (g b)
    intro x y ho h0 h1 h2
    apply hcell b x y ho
    intro i hi
    simp only [baseCoordinates, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨table, ht, hs⟩ := recover_world_lists reference p q hp hq
    (fun w => ENNReal.ofReal (ω w)) hv γ (meshCode ![ρ, ρ, ρ]) (meshCode_measurable _)
    (meshCorner ![ρ, ρ, ρ]) (meshCode_corner _ (by intro i; fin_cases i <;> exact hρ))
    hqc K L hL hLK
  have htm (w) (b) : MeasurableSet {o | b ∈ table w (meshCode ![ρ, ρ, ρ] o)} :=
    (meshCode_measurable _) ((Set.to_countable {c | b ∈ table w c}).measurableSet)
  have he (b : Fin C) :
      (∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂reference) ≤
        densityL1Distance volume (g b) (f b) := by
    have hh := pureMarginal_ediff_le (B (γ b)) a
      (ENNReal.measurable_ofReal.comp (hf b)) (ENNReal.measurable_ofReal.comp (hg b))
    simp only [Function.comp_apply] at hh
    simp_rw [ediff_ofReal _ _ (hf0 b _) (hg0 b _)] at hh
    simpa only [p, q, Function.comp_def, ediff, densityL1Distance, abs_sub_comm] using hh
  refine ⟨table, ht, ?_⟩
  have hleft : (∑ b, ENNReal.ofReal (ω (γ b)) * (μ b)
      {z | z ∈ F b ∧ b ∈ L (γ b) (pureMap (B (γ b)) a z)}) =
      ∑ b, ENNReal.ofReal (ω (γ b)) *
        ∫⁻ x, {x | b ∈ L (γ b) x}.indicator (p b) x ∂reference := by
    apply sum_congr rfl
    intro b _
    exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (ω (γ b)) * z)
      (observation_mass (μ b) (F b) (B (γ b)) a _
        (ENNReal.measurable_ofReal.comp (hf b)) (hraw b) _ (hL (γ b) b))
  have hright : (∑ b, ENNReal.ofReal (ω (γ b)) * (μ b)
      {z | z ∈ F b ∧ b ∈ table (γ b) (meshCode ![ρ, ρ, ρ] (pureMap (B (γ b)) a z))}) =
      ∑ b, ENNReal.ofReal (ω (γ b)) *
        ∫⁻ x, {x | b ∈ table (γ b) (meshCode ![ρ, ρ, ρ] x)}.indicator (p b) x ∂reference := by
    apply sum_congr rfl
    intro b _
    exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (ω (γ b)) * z)
      (observation_mass (μ b) (F b) (B (γ b)) a _
        (ENNReal.measurable_ofReal.comp (hf b)) (hraw b) _ (htm (γ b) b))
  rw [hleft, hright]
  exact hs.trans (add_le_add le_rfl (mul_le_mul_right (sum_le_sum (fun b _ => he b)) 2))

end Submission.Obl.k4_original_observation_atlas_encoding
