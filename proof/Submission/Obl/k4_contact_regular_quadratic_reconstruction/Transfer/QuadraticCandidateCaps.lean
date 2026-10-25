/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/QuadraticCandidateCaps.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
/- The finite-code summation helper is adapted from this LOT tree, obligation
   o223, session x0775, commit a7a28ad1,
   Submission/Obl/k4_contact_parent_horizontal_reduction/QuadraticFiberCaps.lean. -/
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

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


/-- A regular frozen quadratic needs only boundedly many ORIGINAL hidden
bins. Any unchanged original velocity numerator in cap is retained. -/
theorem regular_quadratic_original_bin_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E T : Set Ω) (hET : E ⊆ T) (hidden : Ω → ℝ)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 2)
    {ε β δ : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hδ : 0 < δ)
    (hregular : ∀ᵐ p ∂μ, p ∈ E → |f.eval (hidden p)| ≤ ε ∧
      β ≤ |f.derivative.eval (hidden p)|)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ T ∧ ⌊hidden p / δ⌋ = a} ≤ cap) :
    μ E ≤ ENNReal.ofReal (8 * (1 + ε / (β * δ))) * cap := by
  classical
  let B := (fun x : ℝ => ⌊(x - 0) / δ⌋) ''
    {x : ℝ | |f.eval x| ≤ ε ∧ β ≤ |f.derivative.eval x|}
  have hbins := grid_bins_quadratic_sublevel f hf hε hβ hδ 0
  let good : Set Ω := {p | p ∈ E ∧ |f.eval (hidden p)| ≤ ε ∧
    β ≤ |f.derivative.eval (hidden p)|}
  have hgood : μ E ≤ μ good := by
    apply measure_mono_ae
    filter_upwards [hregular] with p hp hpE
    exact ⟨hpE, hp hpE⟩
  have hmass : μ good ≤ (B.ncard : ENNReal) * cap := by
    apply measure_le_finite_code_cap μ good (fun p => ⌊hidden p / δ⌋) B hbins.1
    · intro p hp
      exact ⟨hidden p, hp.2, by simp⟩
    · intro a _
      have hsub : {p | p ∈ good ∧ ⌊hidden p / δ⌋ = a} ⊆
          {p | p ∈ T ∧ ⌊hidden p / δ⌋ = a} := fun p hp => ⟨hET hp.1.1, hp.2⟩
      exact (measure_mono hsub).trans (hcap a)
  have hcard : (B.ncard : ENNReal) ≤ ENNReal.ofReal (8 * (1 + ε / (β * δ))) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hbins.2
  exact hgood.trans (hmass.trans (mul_le_mul' hcard le_rfl))

/-- Freezing a candidate test on one sufficiently fine base cell gives the
regular-bin bound. In particular both its original scalar thickness and
its original velocity numerator are charged together. -/
theorem frozen_candidate_original_bin_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E T : Set Ω) (hET : E ⊆ T) (hidden value derivative : Ω → ℝ)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 2)
    {H c β : ℝ} (hH : 0 ≤ H) (hc : 0 < c) (hβ : 0 < β)
    (hgood : ∀ᵐ p ∂μ, p ∈ E → |value p| ≤ H * c ∧ β ≤ |derivative p| ∧
      |f.eval (hidden p) - value p| ≤ H * c ∧
      |f.derivative.eval (hidden p) - derivative p| ≤ β / 2)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ T ∧ ⌊hidden p / c⌋ = a} ≤ cap) :
    μ E ≤ ENNReal.ofReal (8 * (1 + 4 * H / β)) * cap := by
  have hregular : ∀ᵐ p ∂μ, p ∈ E → |f.eval (hidden p)| ≤ 2 * H * c ∧
      β / 2 ≤ |f.derivative.eval (hidden p)| := by
    filter_upwards [hgood] with p hp hpE
    obtain ⟨hv, hd, hfv, hfd⟩ := hp hpE
    constructor
    · have hh := (abs_add_le (f.eval (hidden p) - value p) (value p))
      rw [sub_add_cancel] at hh
      linarith
    · have hh := abs_sub_abs_le_abs_sub (derivative p) (f.derivative.eval (hidden p))
      rw [abs_sub_comm (derivative p)] at hh
      linarith
  have hh := regular_quadratic_original_bin_cap μ E T hET hidden f hf
    (by positivity : 0 ≤ 2 * H * c) (by positivity : 0 < β / 2) hc hregular cap hcap
  have he : 8 * (1 + (2 * H * c) / ((β / 2) * c)) = 8 * (1 + 4 * H / β) := by
    field_simp <;> ring
  simpa only [he] using hh

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
