import Submission.Obl.k4_native_base_flattening.PolynomialAveraging
import Submission.Obl.k4_native_base_flattening.Shear
import Submission.Obl.k4_native_base_flattening.Observation
import Submission.Obl.k4_native_base_flattening.Labels

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Lib.K4ModelReduction
open Submission.Obl.k4_profile_density_bounds (Observation reference)
open scoped ENNReal

/-- Cube support in the seven sheared coordinates yields support in both product factors. -/
lemma joined_density_support {L : ℝ} (g : (Fin 7 → ℝ) → ℝ)
    (hs : supportedInCube g L) :
    ∀ q : (Fin 3 → ℝ) × (Fin 4 → ℝ), ENNReal.ofReal (g (join q)) ≠ 0 →
      (∀ i, |q.1 i| ≤ L) ∧ (∀ i, |q.2 i| ≤ L) := by
  intro q hq
  have hreal : g (join q) ≠ 0 := by
    intro hz
    simp only [hz, ENNReal.ofReal_zero, ne_eq, not_true_eq_false] at hq
  have hx : ∀ i, |join q i| ≤ L := by
    intro i
    by_contra hi
    exact hreal (hs _ i (lt_of_not_ge hi))
  constructor
  · intro i
    fin_cases i
    · exact hx 0
    · exact hx 1
    · exact hx 2
  · intro i
    fin_cases i
    · exact hx 3
    · exact hx 4
    · exact hx 5
    · exact hx 6

/-- The three base mesh coordinates remain the base coordinates after the product split. -/
lemma joined_density_base_cells (n : ℝ) (H : ℕ) (g : (Fin 7 → ℝ) → ℝ)
    (hc : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊n ^ H * x i⌋ = ⌊n ^ H * y i⌋) → g x = g y) :
    ∀ z z' : Fin 3 → ℝ, ∀ w : Fin 4 → ℝ,
      (∀ i, ⌊n ^ H * z i⌋ = ⌊n ^ H * z' i⌋) →
        ENNReal.ofReal (g (join (z, w))) = ENNReal.ofReal (g (join (z', w))) := by
  intro z z' w hz
  apply congrArg ENNReal.ofReal
  apply hc
  · intro i hi
    fin_cases i <;> simp_all [baseCoordinates, join]
  · intro i hi
    simp only [baseCoordinates, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hz 0
    · exact hz 1
    · exact hz 2

/-- The marginal of the averaged real source satisfies the common-label cell hypothesis. -/
lemma marg_base_mesh_constant (n : ℝ) (H : ℕ) (a b : ℝ)
    (g : (Fin 7 → ℝ) → ℝ)
    (hc : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊n ^ H * x i⌋ = ⌊n ^ H * y i⌋) → g x = g y) :
    ObservationBaseMeshConstant n H
      (marg a b (fun q => ENNReal.ofReal (g (join q)))) := by
  intro x x' h v hx
  apply marg_eq_of_cell a b ((n ^ H)⁻¹)
  · intro z z' w hz
    apply joined_density_base_cells n H g hc z z' w
    intro i
    simpa only [div_inv_eq_mul, mul_comm] using hz i
  · intro i
    simpa only [div_inv_eq_mul, mul_comm] using hx i

/-- The symmetric truncated difference agrees with the real absolute difference on
nonnegative finite values. -/
lemma ediff_ofReal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ediff (ENNReal.ofReal a) (ENNReal.ofReal b) = ENNReal.ofReal |a - b| := by
  by_cases hab : a ≤ b
  · rw [ediff, tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hab), zero_add,
      ← ENNReal.ofReal_sub _ ha, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    rw [ediff, tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hba), add_zero,
      ← ENNReal.ofReal_sub _ hb, abs_of_nonneg (sub_nonneg.mpr hba)]

/-- The volume-preserving product split keeps the exact L1 error of real source densities. -/
lemma joined_density_lintegral_ediff (f g : (Fin 7 → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ q : (Fin 3 → ℝ) × (Fin 4 → ℝ),
      ediff (ENNReal.ofReal (f (join q))) (ENNReal.ofReal (g (join q)))
        ∂((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))) =
      densityL1Distance volume f g := by
  simp_rw [ediff_ofReal _ _ (hf0 _) (hg0 _)]
  exact measurePreserving_join.lintegral_comp
    (ENNReal.measurable_ofReal.comp (hf.sub hg).abs)

end Submission.Obl.k4_native_base_flattening
