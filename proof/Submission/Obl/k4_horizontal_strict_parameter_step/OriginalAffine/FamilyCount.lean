/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/FamilyCount.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeMeshCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.CountNumerics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Count fine labels by their whole original disjoint witnesses in a common
thin box and a parent affine band.  None of the witness floors is replaced by
the mass of the current-law restriction of that label. -/
theorem original_affine_band_family_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (E : ι → Set Ω)
    (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (g : Fin 3 → ℝ)
    (c t₀ z₀ y₀ l₁ l₂ l₃ R₀ R₁ R₂ η a K M m : ℝ)
    (hη : 0 < η) (ha : 0 < a) (hK : 0 ≤ K) (hM : 0 ≤ M) (hm : 0 < m)
    (hg₀ : η ≤ R₀) (hg₁ : (|l₁| + 1) * η ≤ R₁)
    (hg₂ : (|l₂| + |l₃| + 1) * η ≤ R₂)
    (hresolve : η * ∑ j, |g j| ≤ a)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = q ∧ ⌊f ω / a⌋ = j} ≤
        ENNReal.ofReal (M * η ^ 3))
    (hEm : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (E i))
    (hbox : ∀ i ∈ S, ∀ ω ∈ E i, |z ω 0 - t₀| ≤ R₀ ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ R₁ ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ R₂)
    (hfit : ∀ i ∈ S, ∀ ω ∈ E i, |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a) :
    (S.card : ℝ) ≤ (64 * (2 * K + 7) * M * R₀ * R₁ * R₂) / m := by
  classical
  let U := ⋃ i ∈ S, E i
  have hUbox (ω : Ω) (hω : ω ∈ U) : |z ω 0 - t₀| ≤ R₀ ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ R₁ ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ R₂ := by
    obtain ⟨i, hi, hω⟩ := mem_iUnion₂.mp hω
    exact hbox i hi ω hω
  have hUfit (ω : Ω) (hω : ω ∈ U) : |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a := by
    obtain ⟨i, hi, hω⟩ := mem_iUnion₂.mp hω
    exact hfit i hi ω hω
  have hupper := tilted_affine_band_mass μ z f g c t₀ z₀ y₀ l₁ l₂ l₃
    R₀ R₁ R₂ η a K M hη ha hK hM hg₀ hg₁ hg₂ hresolve hcap hUbox hUfit
  have hlower : ENNReal.ofReal ((S.card : ℝ) * m) ≤ μ U := by
    calc
      _ = ∑ _i ∈ S, ENNReal.ofReal m := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, μ (E i) := Finset.sum_le_sum (fun i hi => hfloor i hi)
      _ = μ U := (measure_biUnion_finset hdisj hEm).symm
  have hR₀ : 0 ≤ R₀ := hη.le.trans hg₀
  have hR₁ : 0 ≤ R₁ := (by positivity : 0 ≤ (|l₁| + 1) * η).trans hg₁
  have hR₂ : 0 ≤ R₂ := (by positivity : 0 ≤ (|l₂| + |l₃| + 1) * η).trans hg₂
  apply (le_div_iff₀ hm).mpr
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlower.trans hupper)

/-- Original child mass, a single common contact box, and the inherited
parent band give the all-width scalar support count.  The transverse side is
quadratic and every witness is charged under its unrestricted original law. -/
theorem original_child_support_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (E : ι → Set Ω)
    (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (g : Fin 3 → ℝ)
    (c t₀ z₀ y₀ l₁ l₂ l₃ K q η a₀ w d : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hη : 0 < η) (ha₀ : 0 < a₀) (hw : 0 < w)
    (hmesh₀ : η ≤ q / 2) (hmesh₁ : (|l₁| + 1) * η ≤ 8 * K ^ 2 * q)
    (hmesh₂ : (|l₂| + |l₃| + 1) * η ≤ 32 * K ^ 4 * q ^ 2)
    (hresolve : η * ∑ j, |g j| ≤ a₀)
    (hcap : ∀ (p : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = p ∧ ⌊f ω / a₀⌋ = j} ≤
        ENNReal.ofReal (K * a₀ ^ d * η ^ 3))
    (hEm : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (q ^ 4 * (w * a₀) ^ d / K ^ 3) ≤ μ (E i))
    (hbox : ∀ i ∈ S, ∀ ω ∈ E i, |z ω 0 - t₀| ≤ q / 2 ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ 8 * K ^ 2 * q ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ 32 * K ^ 4 * q ^ 2)
    (hparent : ∀ i ∈ S, ∀ ω ∈ E i, |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a₀) :
    (S.card : ℝ) ≤ 73728 * K ^ 11 * w ^ (-d) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hb := original_affine_band_family_count μ S E z f g c t₀ z₀ y₀ l₁ l₂ l₃
    (q / 2) (8 * K ^ 2 * q) (32 * K ^ 4 * q ^ 2) η a₀ K (K * a₀ ^ d)
    (q ^ 4 * (w * a₀) ^ d / K ^ 3) hη ha₀ hKp.le (by positivity) (by positivity)
    hmesh₀ hmesh₁ hmesh₂ hresolve hcap hEm hdisj hfloor hbox hparent
  exact hb.trans (original_common_box_count_ratio hK hq ha₀ hw)

end Submission.Obl.k4_horizontal_strict_parameter_step
