import Submission.Lib.K4PolynomialPotential.Transverse

/-!
Adapted from: here:o062
Original proof: x0212, commit e5b8362,
Submission/Obl/k4_scalar_mesh_projection/TransverseFibers.lean.

Fubini forms of the polynomial regular-sublevel estimate. The base law and
all incidence masses stay unnormalized. The sum of base-cell volumes is
retained explicitly, including repeated cells with different height bins.
-/

namespace Submission.Lib.K4PolynomialPotential

open Set MeasureTheory

/-- A measurable incidence set in a base-dependent polynomial height
window has mass bounded by base mass times the regular-fiber length. -/
theorem polynomial_regular_fiber_mass_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P : α → Polynomial ℝ) (S : Set (α × ℝ)) (E : Set α)
    (c : α → ℝ) (D : ℕ) {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hbase : ∀ z ∈ S, z.1 ∈ E)
    (hdegree : ∀ x ∈ E, (P x).natDegree ≤ D)
    (hwindow : ∀ z ∈ S, |(P z.1).eval z.2 - c z.1| ≤ ε)
    (hderiv : ∀ z ∈ S, b ≤ |(P z.1).derivative.eval z.2|) :
    (μ.prod volume) S ≤ μ E * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ x, volume (Prod.mk x ⁻¹' S) ∂μ) ≤
        ∫⁻ x, E.indicator (fun _ => ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        calc
          volume (Prod.mk x ⁻¹' S) ≤
              volume {t : ℝ | |(P x).eval t - c x| ≤ ε ∧ b ≤ |(P x).derivative.eval t|} :=
            measure_mono (fun t ht => ⟨hwindow (x, t) ht, hderiv (x, t) ht⟩)
          _ ≤ ENNReal.ofReal (4 * (((P x).natDegree : ℝ) + 1) * ε / b) :=
            volume_polynomial_regular_height_window (P x) (c x) hε hb
          _ ≤ ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
            apply ENNReal.ofReal_le_ofReal
            gcongr
            exact_mod_cast hdegree x hx
      · have hempty : Prod.mk x ⁻¹' S = ∅ := by
          ext t
          simp only [mem_preimage, mem_empty_iff_false, iff_false]
          exact fun ht => hx (hbase (x, t) ht)
        simp only [hempty, measure_empty, Set.indicator_of_notMem hx, le_refl]
    _ = μ E * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
      rw [lintegral_indicator_const hE, mul_comm]

/-- For a polynomial family over an arbitrary base, a finite collection of
endpoint cells costs the sum of their base measures times their height width.
Only the actual incidence set is required to pass the derivative test. -/
theorem polynomial_regular_endpoint_cells_mass_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (P : α → Polynomial ℝ) (S : Set (α × ℝ))
    (F : Finset ι) (E : ι → Set α) (c : ι → ℝ) (D : ℕ)
    {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (heval : Measurable (fun z : α × ℝ => (P z.1).eval z.2))
    (hdegree : ∀ x, (P x).natDegree ≤ D)
    (hcover : ∀ z ∈ S, ∃ i ∈ F, z.1 ∈ E i ∧ |(P z.1).eval z.2 - c i| ≤ ε)
    (hderiv : ∀ z ∈ S, b ≤ |(P z.1).derivative.eval z.2|) :
    (μ.prod volume) S ≤ (∑ i ∈ F, μ (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
  classical
  let cell (i : ι) : Set (α × ℝ) :=
    {z | z ∈ S ∧ z.1 ∈ E i ∧ |(P z.1).eval z.2 - c i| ≤ ε}
  have hcell (i : ι) (hi : i ∈ F) : MeasurableSet (cell i) :=
    hS.inter (((hE i hi).preimage measurable_fst).inter
      (measurableSet_le (heval.sub_const (c i)).abs measurable_const))
  have hcell_mass (i : ι) (hi : i ∈ F) :
      (μ.prod volume) (cell i) ≤ μ (E i) *
        ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
    apply polynomial_regular_fiber_mass_le μ P (cell i) (E i) (fun _ => c i) D
      hε hb (hcell i hi) (hE i hi)
    · exact fun z hz => hz.2.1
    · exact fun x hx => hdegree x
    · exact fun z hz => hz.2.2
    · exact fun z hz => hderiv z hz.1
  have hcover' : S ⊆ ⋃ i ∈ F, cell i := by
    intro z hz
    obtain ⟨i, hi, hzi, hzw⟩ := hcover z hz
    simp only [mem_iUnion]
    exact ⟨i, hi, hz, hzi, hzw⟩
  calc
    (μ.prod volume) S ≤ (μ.prod volume) (⋃ i ∈ F, cell i) := measure_mono hcover'
    _ ≤ ∑ i ∈ F, (μ.prod volume) (cell i) := measure_biUnion_finset_le F cell
    _ ≤ ∑ i ∈ F, μ (E i) * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) :=
      Finset.sum_le_sum (fun i hi => hcell_mass i hi)
    _ = (∑ i ∈ F, μ (E i)) * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / b) := by
      rw [Finset.sum_mul]

end Submission.Lib.K4PolynomialPotential
