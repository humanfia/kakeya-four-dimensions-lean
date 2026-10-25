/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- A bounded-rectangle version of the long-label mass estimate in accepted
o016's Measure.lean. Large product mass forces many fibers with a fixed
fraction of the average fiber mass. -/
theorem exists_many_large_fibers {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (S : Set α) (T : Set β) (E : Set (α × β)) (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hrect : E ⊆ S ×ˢ T) (A B ℓ : ℝ) (hA : 0 < A) (hB : 0 < B) (hℓ : 0 < ℓ)
    (hμS : μ S ≤ ENNReal.ofReal A) (hνT : ν T ≤ ENNReal.ofReal B)
    (hmass : ENNReal.ofReal ℓ ≤ (μ.prod ν) E) :
    ∃ G : Set α, MeasurableSet G ∧ G ⊆ S ∧ ENNReal.ofReal (ℓ / (2 * B)) ≤ μ G ∧
      ∀ x ∈ G, ENNReal.ofReal (ℓ / (2 * A)) ≤ ν (Prod.mk x ⁻¹' E) := by
  classical
  let f : α → ENNReal := fun x => ν (Prod.mk x ⁻¹' E)
  let a : ENNReal := ENNReal.ofReal (ℓ / (2 * A))
  let b : ENNReal := ENNReal.ofReal B
  let G : Set α := S ∩ {x | a ≤ f x}
  have hf : Measurable f := measurable_measure_prodMk_left hE
  have hG : MeasurableSet G := hS.inter (measurableSet_le measurable_const hf)
  have hGS : G ⊆ S := Set.inter_subset_left
  have hfb (x : α) : f x ≤ b :=
    (measure_mono (show Prod.mk x ⁻¹' E ⊆ T from fun y hy => (hrect hy).2)).trans hνT
  have hfzero (x : α) (hx : x ∉ S) : f x = 0 := by
    have he : Prod.mk x ⁻¹' E = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hx (hrect hy).1
    simp [f, he]
  have hpoint (x : α) : f x ≤ S.indicator (fun _ => a) x + G.indicator (fun _ => b) x := by
    by_cases hxS : x ∈ S
    · by_cases hxG : x ∈ G
      · simp only [Set.indicator_of_mem hxS, Set.indicator_of_mem hxG]
        exact (hfb x).trans (le_add_of_nonneg_left bot_le)
      · have hnot : ¬ a ≤ f x := fun h => hxG ⟨hxS, h⟩
        simpa only [Set.indicator_of_mem hxS, Set.indicator_of_notMem hxG, add_zero] using
          (lt_of_not_ge hnot).le
    · simp only [hfzero x hxS, Set.indicator_of_notMem hxS, zero_add]
      exact bot_le
  have hI : (μ.prod ν) E ≤ a * μ S + b * μ G := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, S.indicator (fun _ => a) x + G.indicator (fun _ => b) x ∂μ :=
        lintegral_mono hpoint
      _ = _ := by
        rw [lintegral_add_left (measurable_const.indicator hS),
          lintegral_indicator_const hS, lintegral_indicator_const hG]
  have haA : a * ENNReal.ofReal A = ENNReal.ofReal (ℓ / 2) := by
    dsimp [a]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    <;> ring
  have hbudget : ENNReal.ofReal ℓ ≤ ENNReal.ofReal (ℓ / 2) + b * μ G := by
    apply hmass.trans (hI.trans _)
    calc
      a * μ S + b * μ G ≤ a * ENNReal.ofReal A + b * μ G := by gcongr
      _ = _ := by rw [haA]
  have hGtop : μ G ≠ ⊤ := ne_of_lt ((measure_mono hGS).trans_lt (hμS.trans_lt ENNReal.ofReal_lt_top))
  have hbtop : b * μ G ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGtop
  have hsumtop : ENNReal.ofReal (ℓ / 2) + b * μ G ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hbtop⟩
  have hreal : ℓ ≤ ℓ / 2 + B * (μ G).toReal := by
    have h := ENNReal.toReal_mono hsumtop hbudget
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hbtop, ENNReal.toReal_mul] at h
    simpa only [b, ENNReal.toReal_ofReal hℓ.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ ℓ / 2), ENNReal.toReal_ofReal hB.le] using h
  refine ⟨G, hG, hGS, ENNReal.ofReal_le_of_le_toReal ?_, fun x hx => hx.2⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

end Submission.Lib.K4PolynomialNorming
