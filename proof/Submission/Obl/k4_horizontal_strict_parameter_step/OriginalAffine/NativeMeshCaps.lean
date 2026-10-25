/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeMeshCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/NativeMeshCaps.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.TiltedMesh
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

/-! Native finite mesh caps near affine fits, with the original law and tilted volume retained. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Discrete cell/bin ceilings also bound a moving signal band on finitely
many original base cells. The reference is counting measure on the cells. -/
lemma moving_band_mass_from_cell_caps {Ω I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (tag : Ω → I) (f : Ω → ℝ) (center : I → ℝ)
    {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (cap : ENNReal)
    (hcap : ∀ q j, μ {ω | tag ω = q ∧ ⌊f ω / a⌋ = j} ≤ cap)
    (V : Finset I) {E : Set Ω}
    (hcover : ∀ ω ∈ E, tag ω ∈ V)
    (hband : ∀ ω ∈ E, |f ω - center (tag ω)| ≤ K * a) :
    μ E ≤ ENNReal.ofReal (2 * K + 5) * cap * (V.card : ENNReal) := by
  classical
  have hmarg (j : ℤ) (S : Set I) (_hS : MeasurableSet S) :
      μ {ω | tag ω ∈ S ∧ ⌊f ω / a⌋ = j} ≤ cap * Measure.count S := by
    have hsub : {ω | tag ω ∈ S ∧ ⌊f ω / a⌋ = j} ⊆
        ⋃ q : S, {ω | tag ω = q.val ∧ ⌊f ω / a⌋ = j} := by
      intro ω hω
      exact mem_iUnion.mpr ⟨⟨tag ω, hω.1⟩, rfl, hω.2⟩
    calc μ {ω | tag ω ∈ S ∧ ⌊f ω / a⌋ = j}
        ≤ μ (⋃ q : S, {ω | tag ω = q.val ∧ ⌊f ω / a⌋ = j}) := measure_mono hsub
      _ ≤ ∑' q : S, μ {ω | tag ω = q.val ∧ ⌊f ω / a⌋ = j} := measure_iUnion_le _
      _ ≤ ∑' _q : S, cap := ENNReal.tsum_le_tsum (fun q => hcap q.val j)
      _ = cap * ∑' _q : S, (1 : ENNReal) := by
        rw [← ENNReal.tsum_mul_left]
        simp only [mul_one]
      _ ≤ cap * Measure.count S := mul_le_mul' le_rfl Measure.le_count_apply
  have h := Submission.Obl.k4_fixed_budget_quadratic_recovery.moving_interval_cap
    μ Measure.count tag f ha hK cap hmarg center (measurable_of_countable center)
    (V : Set I) V.measurableSet
  have hsub : E ⊆ {ω | tag ω ∈ (V : Set I) ∧ |f ω - center (tag ω)| ≤ K * a} := by
    intro ω hω
    exact ⟨hcover ω hω, hband ω hω⟩
  have h' : μ {ω | tag ω ∈ (V : Set I) ∧ |f ω - center (tag ω)| ≤ K * a} ≤
      ENNReal.ofReal (2 * K + 5) * cap * (V.card : ENNReal) := by
    simpa only [Measure.count_apply_finset] using h
  exact (measure_mono hsub).trans h'

/-- Variation of an affine predictor inside one original base mesh cell. -/
lemma affine_mesh_center_error {η : ℝ} (hη : 0 < η) (g z : Fin 3 → ℝ) (c : ℝ) :
    |(c + ∑ j, g j * z j) -
      (c + ∑ j, g j * ((⌊z j / η⌋ : ℝ) * η))| ≤ η * ∑ j, |g j| := by
  have heq : (c + ∑ j, g j * z j) -
      (c + ∑ j, g j * ((⌊z j / η⌋ : ℝ) * η)) =
        ∑ j, g j * (z j - (⌊z j / η⌋ : ℝ) * η) := by
    simp only [Fin.sum_univ_succ]
    ring
  rw [heq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin 3, |g j * (z j - (⌊z j / η⌋ : ℝ) * η)|
      ≤ ∑ j : Fin 3, η * |g j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (floor_mesh_error hη (z j)) (abs_nonneg _)
    _ = η * ∑ j : Fin 3, |g j| := (Finset.mul_sum _ _ _).symm

/-- Pure original mesh ceilings near an affine signal give the correct volume
bound on a tilted box, without any continuous base-density assertion. -/
lemma tilted_affine_band_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ)
    (g : Fin 3 → ℝ) (c t₀ z₀ y₀ l₁ l₂ l₃ R₀ R₁ R₂ η a K M : ℝ)
    (hη : 0 < η) (ha : 0 < a) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg₀ : η ≤ R₀) (hg₁ : (|l₁| + 1) * η ≤ R₁)
    (hg₂ : (|l₂| + |l₃| + 1) * η ≤ R₂)
    (hresolve : η * ∑ j, |g j| ≤ a)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = q ∧ ⌊f ω / a⌋ = j} ≤
        ENNReal.ofReal (M * η ^ 3))
    {E : Set Ω}
    (hbox : ∀ ω ∈ E, |z ω 0 - t₀| ≤ R₀ ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ R₁ ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ R₂)
    (hfit : ∀ ω ∈ E, |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a) :
    μ E ≤ ENNReal.ofReal (64 * (2 * K + 7) * M * R₀ * R₁ * R₂) := by
  classical
  obtain ⟨V, hVcard, hV⟩ := exists_triangular_mesh_volume t₀ z₀ y₀ l₁ l₂ l₃
    R₀ R₁ R₂ η hη hg₀ hg₁ hg₂
  let tag : Ω → Fin 3 → ℤ := fun ω j => ⌊z ω j / η⌋
  let center : (Fin 3 → ℤ) → ℝ := fun q => c + ∑ j, g j * ((q j : ℝ) * η)
  have hcover (ω : Ω) (hω : ω ∈ E) : tag ω ∈ V := by
    have h := hV (z ω 0) (z ω 1) (z ω 2) (hbox ω hω).1
      (hbox ω hω).2.1 (hbox ω hω).2.2
    have heq : tag ω = ![⌊z ω 0 / η⌋, ⌊z ω 1 / η⌋, ⌊z ω 2 / η⌋] := by
      funext j
      fin_cases j <;> rfl
    rw [heq]
    exact h
  have hband (ω : Ω) (hω : ω ∈ E) : |f ω - center (tag ω)| ≤ (K + 1) * a := by
    have hvar := (affine_mesh_center_error hη g (z ω) c).trans hresolve
    have hid : f ω - center (tag ω) =
        (f ω - (c + ∑ j, g j * z ω j)) +
        ((c + ∑ j, g j * z ω j) - center (tag ω)) := by ring
    rw [hid]
    have hvar' : |(c + ∑ j, g j * z ω j) - center (tag ω)| ≤ a := hvar
    exact (abs_add_le _ _).trans (by nlinarith [hfit ω hω])
  have hmass := moving_band_mass_from_cell_caps (K := K + 1) μ tag f center ha (by linarith)
    (ENNReal.ofReal (M * η ^ 3)) hcap V hcover hband
  have hK' : 0 ≤ 2 * K + 7 := by positivity
  have hprod : (2 * K + 7) * (M * η ^ 3) * (V.card : ℝ) =
      (2 * K + 7) * M * ((V.card : ℝ) * η ^ 3) := by ring
  calc μ E ≤ ENNReal.ofReal (2 * (K + 1) + 5) *
        ENNReal.ofReal (M * η ^ 3) * (V.card : ENNReal) := hmass
    _ = ENNReal.ofReal ((2 * K + 7) * M * ((V.card : ℝ) * η ^ 3)) := by
      rw [show 2 * (K + 1) + 5 = 2 * K + 7 by ring,
        ← ENNReal.ofReal_mul hK', ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity), hprod]
    _ ≤ ENNReal.ofReal ((2 * K + 7) * M * (64 * R₀ * R₁ * R₂)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hVcard (by positivity)
    _ = _ := by congr 1; ring

end Submission.Obl.k4_horizontal_strict_parameter_step
