-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/Recovery.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Jitter

/-!
Measure-theoretic recovery of scalar packets: selecting one common jitter,
pruning by the original reference floors, and measurability of whole-time fits.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory
open scoped ENNReal

/-- Fubini selects a single jitter vector for the entire successful assignment.
The vector can also be required to lie in any prescribed set of full measure. -/
theorem exists_common_jitter {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Measure X) [IsFiniteMeasure κ]
    {E : Set (Ω × X)} (hE : MeasurableSet E) {G : Set Ω} (hG : ρ Gᶜ = 0) :
    ∃ δ ∈ G, (ρ.prod κ) E ≤ κ (Prod.mk δ ⁻¹' E) := by
  have hf : (∫⁻ δ, κ (Prod.mk δ ⁻¹' E) ∂ρ) ≠ ∞ := by
    rw [← Measure.prod_apply hE]
    exact measure_ne_top _ _
  obtain ⟨δ, hδ, h⟩ := exists_notMem_null_lintegral_le hf hG
  exact ⟨δ, by simpa using hδ, by simpa only [Measure.prod_apply hE] using h⟩

/-- Pruning uses a fixed sum of reference weights. There is no renormalization
of the active law, and no measurability or disjointness is needed for this bound. -/
theorem prune_small_labels {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (I : Finset ι) (A : ι → Set X) (R : ι → ℝ≥0∞) {τ B : ℝ≥0∞}
    (hR : ∑ i ∈ I, R i ≤ B) :
    ∃ F : Finset ι, F ⊆ I ∧ (∀ i ∈ F, τ * R i ≤ μ (A i)) ∧
      μ (⋃ i ∈ I, A i) ≤ μ (⋃ i ∈ F, A i) + τ * B := by
  classical
  let F := I.filter (fun i => τ * R i ≤ μ (A i))
  have hF : F ⊆ I := Finset.filter_subset _ _
  have hbad : μ (⋃ i ∈ I \ F, A i) ≤ τ * B := by
    calc
      μ (⋃ i ∈ I \ F, A i) ≤ ∑ i ∈ I \ F, μ (A i) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ I \ F, τ * R i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_sdiff.mp hi
        have hn : ¬ τ * R i ≤ μ (A i) := by
          intro h
          exact hi'.2 (Finset.mem_filter.mpr ⟨hi'.1, h⟩)
        exact (lt_of_not_ge hn).le
      _ = τ * ∑ i ∈ I \ F, R i := by rw [Finset.mul_sum]
      _ ≤ τ * ∑ i ∈ I, R i := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset (f := R)
          (Finset.sdiff_subset : I \ F ⊆ I)) (show 0 ≤ τ from bot_le)
      _ ≤ τ * B := mul_le_mul_of_nonneg_left hR (show 0 ≤ τ from bot_le)
  have hcover : (⋃ i ∈ I, A i) ⊆ (⋃ i ∈ F, A i) ∪ (⋃ i ∈ I \ F, A i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    by_cases hif : i ∈ F
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, hif, hxi⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hif⟩, hxi⟩)
  refine ⟨F, hF, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

/-- Fix one common jitter, restore the original law, and only then prune by
the unchanged reference numerators. No individual noisy floor is assumed to
survive the selected slice. -/
theorem recover_original_floors_after_common_jitter
    {Ω X Y ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (κ : Measure X) [IsFiniteMeasure κ]
    (μ : Measure Y) {E : Set (Ω × X)} (hE : MeasurableSet E)
    {G : Set Ω} (hG : ρ Gᶜ = 0) (I : Finset ι) (A : Ω → ι → Set Y)
    (R : ι → ℝ≥0∞) {τ θ B : ℝ≥0∞} (hR : ∑ i ∈ I, R i ≤ B)
    (hrestore : ∀ δ ∈ G, τ * κ (Prod.mk δ ⁻¹' E) ≤ μ (⋃ i ∈ I, A δ i)) :
    ∃ δ ∈ G, ∃ F : Finset ι, F ⊆ I ∧
      (∀ i ∈ F, θ * R i ≤ μ (A δ i)) ∧
      τ * (ρ.prod κ) E ≤ μ (⋃ i ∈ F, A δ i) + θ * B := by
  obtain ⟨δ, hδ, hslice⟩ := exists_common_jitter ρ κ hE hG
  obtain ⟨F, hF, hfloor, hmass⟩ := prune_small_labels μ I (A δ) R hR
  refine ⟨δ, hδ, F, hF, hfloor, ?_⟩
  calc
    τ * (ρ.prod κ) E ≤ τ * κ (Prod.mk δ ⁻¹' E) :=
      mul_le_mul_of_nonneg_left hslice (show 0 ≤ τ from bot_le)
    _ ≤ μ (⋃ i ∈ I, A δ i) := hrestore δ hδ
    _ ≤ μ (⋃ i ∈ F, A δ i) + θ * B := hmass

/-- The coefficient set defined by a full-time scalar fit is closed.
This avoids an uncountable-intersection measurability assumption on the prior. -/
theorem isClosed_scalar_fit (P : MvPolynomial (Fin 2) ℝ) (u v R E : ℝ) :
    IsClosed {b : Fin 5 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1,
      |affineTrace b t - u - t * v| ≤ R ∧
      |hiddenTrace b t - MvPolynomial.eval ![t, affineTrace b t] P| ≤ E} := by
  have heq : {b : Fin 5 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1,
      |affineTrace b t - u - t * v| ≤ R ∧
      |hiddenTrace b t - MvPolynomial.eval ![t, affineTrace b t] P| ≤ E} =
      ⋂ t ∈ Icc (0 : ℝ) 1, {b : Fin 5 → ℝ |
        |affineTrace b t - u - t * v| ≤ R ∧
        |hiddenTrace b t - MvPolynomial.eval ![t, affineTrace b t] P| ≤ E} := by
    ext b
    simp
  rw [heq]
  apply isClosed_biInter
  intro t ht
  have hy : Continuous (fun b : Fin 5 → ℝ => affineTrace b t) := by
    dsimp only [affineTrace]
    fun_prop
  have hx : Continuous (fun b : Fin 5 → ℝ => hiddenTrace b t) := by
    dsimp only [hiddenTrace]
    fun_prop
  have hp : Continuous (fun b : Fin 5 → ℝ => MvPolynomial.eval ![t, affineTrace b t] P) := by
    apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using (continuous_const : Continuous (fun _ : Fin 5 → ℝ => t))
    · simpa using hy
  exact (isClosed_le ((hy.sub continuous_const).sub continuous_const).abs continuous_const).inter
    (isClosed_le (hx.sub hp).abs continuous_const)

theorem measurableSet_scalar_fit {α : Type*} [MeasurableSpace α]
    {b : α → Fin 5 → ℝ} (hb : Measurable b)
    (P : MvPolynomial (Fin 2) ℝ) (u v R E : ℝ) :
    MeasurableSet {l : α | ∀ t ∈ Icc (0 : ℝ) 1,
      |affineTrace (b l) t - u - t * v| ≤ R ∧
      |hiddenTrace (b l) t - MvPolynomial.eval ![t, affineTrace (b l) t] P| ≤ E} :=
  (isClosed_scalar_fit P u v R E).measurableSet.preimage hb

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
