-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Geometry; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.FrameBasics

/-!
# Original parent geometry and fine native caps

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation`, files
`Parents.lean` and `NativeCaps.lean`): the parent facts now come from the general
preparation `Parent.Prepared` (`AtDepth`), and the fine caps are the native-signal
(`h = true`) branch of the original caps.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The original parent facts used to integrate a scalar residual cell. -/
structure ParentGeometry (p : Parent α) (k : ℕ) (r : ℝ) : Prop where
  prior_lower : ∀ i : Fin (p.n k r), ENNReal.ofReal
    ((p.N k ^ (-r)) ^ p.d * (((2 : ℝ) ^ p.T k r)⁻¹) ^ 2 *
      p.N k ^ (-p.ℓ * r) / p.K k) ≤ p.ν k (p.A k r i)
  fitted_subset : ∀ i, p.B k r i ⊆ p.A k r i
  coefficient_bound : ∀ i e, |p.c k r i e| ≤ p.K k
  transverse : ∀ i l, l ∈ p.A k r i →
    ∀ t ∈ block (p.T k r) (p.j k r i),
    |p.x k l t 2 - p.c k r i 2 - t * p.c k r i 3 - p.c k r i 4 * p.x k l t 1| ≤
      p.K k * ((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r)

theorem Valid.eventually_parent_geometry (h : p.Valid)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ p.U) :
    ∀ᶠ k in atTop, ParentGeometry p k r := by
  let R := 2 + r⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr]
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ (by linarith : 0 < R) hr).mpr
    dsimp [R]
    linarith
  filter_upwards [h.prepared R hR] with k hk
  have a := hk r hRr hrU
  refine ⟨?_, (fun i => (a.2.2.1 i).2.2),
    (fun i e => (a.2.2.2.2.1 i).2.2.2.1 e), ?_⟩
  · intro i
    simpa only [zpow_neg, zpow_natCast] using (a.2.2.2.2.1 i).1
  · intro i l hl t ht
    simpa only [zpow_neg, zpow_natCast] using
      ((a.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht).2.1

/-- Original fine caps of the native signal, with a whole interval of signal and
angular exponents. The original palette remains a factor in every joint cell. -/
structure FineCaps (p : Parent α) (k : ℕ) (M sMax vMin vMax : ℝ) : Prop where
  pure : ∀ s : ℝ, 0 ≤ s → s ≤ sMax → ∀ (q : Fin 3 → ℤ) (j : ℤ),
    p.μ k {ω | p.z k (p.N k) M ω = q ∧
      ⌊p.signal k ω.1 ω.2 / p.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (p.K k * (p.N k ^ (-M)) ^ 3 * (p.N k ^ (-s)) ^ p.d)
  joint : ∀ s v : ℝ, 0 ≤ s → s ≤ sMax → vMin ≤ v → v ≤ vMax →
    ∀ (q : Fin 3 → ℤ) (j a : ℤ),
    p.μ k {ω | p.z k (p.N k) M ω = q ∧
      ⌊p.signal k ω.1 ω.2 / p.N k ^ (-s)⌋ = j ∧
      ⌊p.b k ω.1 3 / p.N k ^ (-v)⌋ = a} ≤
      ENNReal.ofReal (p.K k * (p.N k ^ (-M)) ^ 3 * (p.N k ^ (-s)) ^ p.d) *
        p.π k {w | ⌊w / p.N k ^ (-v)⌋ = a}
  palette : ∀ v : ℝ, vMin ≤ v → v ≤ vMax → ∀ a : ℤ,
    p.π k {w | ⌊w / p.N k ^ (-v)⌋ = a} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-p.S * v))

/-- Uniform original native caps can be requested on every fixed compact exponent
range; the lower angular endpoint may depend on the requested final loss. -/
theorem Valid.eventually_fine_caps (h : p.Valid)
    {M sMax vMin vMax : ℝ} (hM : 0 < M) (hsMax : 0 ≤ sMax)
    (hvMin : 0 < vMin) (hvMax : vMin ≤ vMax) :
    ∀ᶠ k in atTop, FineCaps p k M sMax vMin vMax := by
  let R := 2 + M + sMax + vMax + M⁻¹ + vMin⁻¹
  have hvMax0 : 0 < vMax := hvMin.trans_le hvMax
  have hR : 1 < R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hR0 : 0 < R := by linarith
  have hMR : M ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hsR : sMax ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hvR : vMax ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hRM : R⁻¹ ≤ M := by
    apply (inv_le_comm₀ hR0 hM).mpr
    dsimp [R]
    linarith [inv_pos.mpr hvMin]
  have hRv : R⁻¹ ≤ vMin := by
    apply (inv_le_comm₀ hR0 hvMin).mpr
    dsimp [R]
    linarith [inv_pos.mpr hM]
  filter_upwards [h.caps R hR] with k hk
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hscale (s : ℝ) : p.N k ^ (-3 * M - p.d * s) =
      (p.N k ^ (-M)) ^ 3 * (p.N k ^ (-s)) ^ p.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    congr 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro s hs hsmax q j
    have hc := (hk M s vMin hRM hMR hs (hsmax.trans hsR) hRv (hvMax.trans hvR)).2.1
      true q j
    simp only [↓reduceIte, hscale] at hc
    simp only [mul_assoc]
    exact hc
  · intro s v hs hsmax hvmin hvmax q j a
    have hc := (hk M s v hRM hMR hs (hsmax.trans hsR) (hRv.trans hvmin)
      (hvmax.trans hvR)).2.2 true q j a
    simp only [↓reduceIte, hscale] at hc
    simp only [mul_assoc]
    exact hc
  · intro v hvmin hvmax a
    exact (hk M 0 v hRM hMR le_rfl (by linarith) (hRv.trans hvmin)
      (hvmax.trans hvR)).1 a

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
