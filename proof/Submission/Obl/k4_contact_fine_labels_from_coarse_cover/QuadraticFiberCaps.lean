-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/QuadraticFiberCaps.lean
import Submission.Lib.K4QuadraticSublevel

-- Adapted from this LOT tree, o223, session x0775, commit 86ba8d3271fa,
-- Submission/Obl/k4_contact_parent_horizontal_reduction/QuadraticFiberCaps.lean.

/-!
# Original-law caps for regular quadratic fibers

The only regularity needed for the native signal is an oscillation bound inside
one fine base state and one hidden-signal bin. The angular bin may be included
in the ambient set `T`, so its original palette weight remains in `cap`.
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory
open Submission.Lib.K4QuadraticSublevel

/-- A finite list of possible codes permits summing original-law ceilings. -/
theorem measure_le_finite_code_cap {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (code : Ω → ι) (B : Set ι) (hB : B.Finite)
    (hcover : ∀ p ∈ S, code p ∈ B) (cap : ENNReal)
    (hcap : ∀ a ∈ B, μ {p | p ∈ S ∧ code p = a} ≤ cap) :
    μ S ≤ (B.ncard : ENNReal) * cap := by
  classical
  let F := hB.toFinset
  have hsub : S ⊆ ⋃ a ∈ F, {p | p ∈ S ∧ code p = a} := by
    intro p hp
    exact mem_iUnion₂.mpr ⟨code p, by simpa [F] using hcover p hp, hp, rfl⟩
  calc
    μ S ≤ μ (⋃ a ∈ F, {p | p ∈ S ∧ code p = a}) := measure_mono hsub
    _ ≤ ∑ a ∈ F, μ {p | p ∈ S ∧ code p = a} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ F, cap := Finset.sum_le_sum fun a ha => hcap a (by simpa [F] using ha)
    _ = (B.ncard : ENNReal) * cap := by
      rw [Set.ncard_eq_toFinset_card B hB]
      simp [F, nsmul_eq_mul]

/-- An oscillation bound transfers native-signal bin ceilings to any set on
which that bound holds. All measures remain the original law. -/
theorem native_signal_cap_of_oscillation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) (hST : S ⊆ T) (native : Ω → ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S, dist (native p) (native p') ≤ L)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ T ∧ ⌊native p / δ⌋ = a} ≤ cap) :
    μ S ≤ ENNReal.ofReal (2 * L / δ + 2) * cap := by
  let B := (fun x : ℝ => ⌊(x - 0) / δ⌋) '' (native '' S)
  have hbins := grid_bins_of_pairwise_dist_le (native '' S) hL hδ 0 (by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    exact hosc p hp p' hp')
  have hmass : μ S ≤ (B.ncard : ENNReal) * cap := by
    apply measure_le_finite_code_cap μ S (fun p => ⌊native p / δ⌋) B hbins.1
    · intro p hp
      exact ⟨native p, ⟨p, hp, rfl⟩, by simp⟩
    · intro a ha
      have hsub : {p | p ∈ S ∧ ⌊native p / δ⌋ = a} ⊆
          {p | p ∈ T ∧ ⌊native p / δ⌋ = a} := fun p hp => ⟨hST hp.1, hp.2⟩
      exact (measure_mono hsub).trans (hcap a)
  have hcard : (B.ncard : ENNReal) ≤ ENNReal.ofReal (2 * L / δ + 2) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hbins.2
  exact hmass.trans (mul_le_mul' hcard le_rfl)

/-- Regular fibers of one frozen quadratic occupy few hidden bins. If the
native signal has bounded oscillation in each such bin, its ORIGINAL bin
ceilings imply a fine-state ceiling. In applications `T` contains the base
state and angular bin, while `S` also contains the stored good-sheet mask. -/
theorem quadratic_fiber_native_signal_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) (hST : S ⊆ T) (hidden native : Ω → ℝ)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 2)
    {ε β δ L : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hregular : ∀ p ∈ S, |f.eval (hidden p)| ≤ ε ∧
      β ≤ |f.derivative.eval (hidden p)|)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S, ⌊hidden p / δ⌋ = ⌊hidden p' / δ⌋ →
      dist (native p) (native p') ≤ L)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ T ∧ ⌊native p / δ⌋ = a} ≤ cap) :
    μ S ≤ ENNReal.ofReal
      (8 * (1 + ε / (β * δ)) * (2 * L / δ + 2)) * cap := by
  let B := (fun x : ℝ => ⌊(x - 0) / δ⌋) ''
    {x : ℝ | |f.eval x| ≤ ε ∧ β ≤ |f.derivative.eval x|}
  have hbins := grid_bins_quadratic_sublevel f hf hε hβ hδ 0
  have hmass : μ S ≤ (B.ncard : ENNReal) *
      (ENNReal.ofReal (2 * L / δ + 2) * cap) := by
    apply measure_le_finite_code_cap μ S (fun p => ⌊hidden p / δ⌋) B hbins.1
    · intro p hp
      exact ⟨hidden p, hregular p hp, by simp⟩
    · intro a ha
      apply native_signal_cap_of_oscillation μ {p | p ∈ S ∧ ⌊hidden p / δ⌋ = a}
        T (fun p hp => hST hp.1) native hδ hL
      · intro p hp p' hp'
        exact hosc p hp.1 p' hp'.1 (hp.2.trans hp'.2.symm)
      · exact hcap
  have hcard : (B.ncard : ENNReal) ≤ ENNReal.ofReal (8 * (1 + ε / (β * δ))) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hbins.2
  calc
    μ S ≤ ENNReal.ofReal (8 * (1 + ε / (β * δ))) *
        (ENNReal.ofReal (2 * L / δ + 2) * cap) :=
      hmass.trans (mul_le_mul' hcard le_rfl)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory

/-- Freezing a test on one original fine base cell keeps its regular fiber.
The resulting cap recovers the original native thickness factor. -/
theorem quadratic_fiber_cap_of_freezing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) (hST : S ⊆ T)
    (hidden native value derivative : Ω → ℝ)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 2)
    {K a B : ℝ} (hK : 0 < K) (ha : 0 < a) (hB : 0 ≤ B)
    (hvalue : ∀ p ∈ S, |value p| ≤ K * a)
    (hderivative : ∀ p ∈ S, K⁻¹ ≤ |derivative p|)
    (hfreeze : ∀ p ∈ S, |f.eval (hidden p) - value p| ≤ K * a ∧
      |f.derivative.eval (hidden p) - derivative p| ≤ (2 * K)⁻¹)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S, ⌊hidden p / a⌋ = ⌊hidden p' / a⌋ →
      dist (native p) (native p') ≤ B * a)
    (cap : ENNReal)
    (hcap : ∀ j : ℤ, μ {p | p ∈ T ∧ ⌊native p / a⌋ = j} ≤ cap) :
    μ S ≤ ENNReal.ofReal (8 * (1 + 4 * K ^ 2) * (2 * B + 2)) * cap := by
  have hregular : ∀ p ∈ S, |f.eval (hidden p)| ≤ 2 * K * a ∧
      (2 * K)⁻¹ ≤ |f.derivative.eval (hidden p)| := by
    intro p hp
    constructor
    · have h' := (abs_add_le (f.eval (hidden p) - value p) (value p))
      simpa only [sub_add_cancel] using
        h'.trans ((add_le_add (hfreeze p hp).1 (hvalue p hp)).trans_eq (by ring))
    · have htriangle : |derivative p| ≤ |f.derivative.eval (hidden p)| +
          |f.derivative.eval (hidden p) - derivative p| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le (derivative p)
          (f.derivative.eval (hidden p)) 0
      have hhalf : K⁻¹ = 2 * (2 * K)⁻¹ := by field_simp
      linarith [hderivative p hp, (hfreeze p hp).2]
  have h := quadratic_fiber_native_signal_cap μ S T hST hidden native f hf
    (by positivity : 0 ≤ 2 * K * a) (inv_pos.mpr (by positivity : 0 < 2 * K)) ha
    (mul_nonneg hB ha.le) hregular hosc cap hcap
  convert h using 1
  congr 2
  field_simp
  ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
