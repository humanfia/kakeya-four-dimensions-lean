/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCollisionCellCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCollisionCellCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! Original-law ceilings for the three coordinates of a collision cell. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped ENNReal

/-- Once the first starting scalar bin and both tangential bins are fixed,
the collision relation confines the second starting scalar to one enlarged
interval. The two factors are measured under the unchanged original prior. -/
theorem original_pair_collision_cell_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (v z : Λ → ℝ)
    {K p d C a a' b D : ℝ} (hK : 0 ≤ K) (hp : 0 < p) (hC : 0 ≤ C)
    (hcap : ∀ a b r : ℝ, p ≤ r →
      ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ z l ∈ Icc b (b + r)} ≤
        K * r ^ (1 + d))
    (E : Set (Λ × Λ))
    (hE : ∀ q ∈ E, q.1 ∈ A ∧ q.2 ∈ A ∧
      v q.1 ∈ Icc a (a + p) ∧ v q.2 ∈ Icc a' (a' + p) ∧
      z q.1 ∈ Icc b (b + p) ∧ |(z q.2 - z q.1) - D| ≤ C * p) :
    (ν.prod ν).real E ≤ (K * p ^ (1 + d)) * (K * ((2 * C + 1) * p) ^ (1 + d)) := by
  let A₁ : Set Λ := {l | l ∈ A ∧ v l ∈ Icc a (a + p) ∧ z l ∈ Icc b (b + p)}
  let A₂ : Set Λ := {l | l ∈ A ∧ v l ∈ Icc a' (a' + (2 * C + 1) * p) ∧
    z l ∈ Icc (b + D - C * p) (b + D - C * p + (2 * C + 1) * p)}
  have hsub : E ⊆ A₁ ×ˢ A₂ := by
    intro q hq
    obtain ⟨h₁, h₂, hv₁, hv₂, hz, he⟩ := hE q hq
    obtain ⟨he₁, he₂⟩ := abs_le.mp he
    exact ⟨⟨h₁, hv₁, hz⟩, ⟨h₂, ⟨hv₂.1, by nlinarith [hv₂.2]⟩, by
      constructor <;> linarith [hz.1, hz.2]⟩⟩
  have hfirst : ν.real A₁ ≤ K * p ^ (1 + d) := hcap a b p le_rfl
  have hsecond : ν.real A₂ ≤ K * ((2 * C + 1) * p) ^ (1 + d) :=
    hcap a' (b + D - C * p) ((2 * C + 1) * p) (by nlinarith)
  calc
    (ν.prod ν).real E ≤ (ν.prod ν).real (A₁ ×ˢ A₂) := measureReal_mono hsub
    _ = ν.real A₁ * ν.real A₂ := measureReal_prod_prod A₁ A₂
    _ ≤ _ := mul_le_mul hfirst hsecond measureReal_nonneg
      (mul_nonneg hK (Real.rpow_nonneg hp.le _))

/-- A time-cell ceiling follows by Tonelli from its original section
ceiling and its time length. No normalized collision prior is introduced. -/
theorem original_spacetime_cell_cap {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) (ν : Measure Λ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {V : Set Θ} (hV : MeasurableSet V)
    (hsub : E ⊆ V ×ˢ univ) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ θ ∈ V, ν.real (Prod.mk θ ⁻¹' E) ≤ C) :
    (μ.prod ν).real E ≤ C * μ.real V := by
  have hb : ∀ θ, ν (Prod.mk θ ⁻¹' E) ≤ V.indicator (fun _ => ENNReal.ofReal C) θ := by
    intro θ
    by_cases hθ : θ ∈ V
    · rw [indicator_of_mem hθ]
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν _)] using
        ENNReal.ofReal_le_ofReal (hcap θ hθ)
    · have he : Prod.mk θ ⁻¹' E = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hθ (hsub hl).1
      simp only [he, measure_empty, indicator_of_notMem hθ, le_refl]
  have hbound : (μ.prod ν) E ≤ ENNReal.ofReal C * μ V := by
    calc
      _ = ∫⁻ θ, ν (Prod.mk θ ⁻¹' E) ∂μ := Measure.prod_apply hE
      _ ≤ ∫⁻ θ, V.indicator (fun _ => ENNReal.ofReal C) θ ∂μ := lintegral_mono hb
      _ = _ := lintegral_indicator_const hV _
  have hfinite : ENNReal.ofReal C * μ V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono hfinite hbound

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
