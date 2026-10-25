import Submission.Obl.k4_raw_localized_native_systems.C.RawGeometry
import Submission.Obl.k4_raw_localized_native_systems.SourceFrames

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The two finite interfaces use the same minor width of the unchanged
original frame. -/
theorem minorWidth_eq_pairing (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    minorWidth Q = Pairing.minorWidth Q := rfl

/-- Current events produced from the later factory layer have genuine
same-world earlier ancestors in the original `sourceFrame` enumeration. -/
theorem CFam.source_frame_ancestry {p : Data} {k M D MC DC m C : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r) (i : ℕ)
    (lst₁ : Fin (p.W k) → Observation → Finset (Fin (levelSet a (i + 1)).card))
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k (levelAtlas a (i + 1) lst₁) MC DC loss g γ n int sp A F lst)
    (c : Fin C) {z : Point} (hz : z ∈ F c) :
    ∃ e : Fin (sourceFrame a ha i).C,
      (sourceFrame a ha i).γ e = γ c ∧ z ∈ (sourceFrame a ha i).F e := by
  obtain ⟨b, hbγ, hbF⟩ := h.earlier_ancestry a ha i (fun _ _ => ∅) lst₁ c hz
  obtain ⟨e, he⟩ := source_layer_index_surj a (levelEmb_lev a i b)
  refine ⟨e, ?_, ?_⟩
  · change a.γ (a.layerEmb i e) = γ c
    rw [he]
    exact hbγ
  · change z ∈ a.F (a.layerEmb i e)
    rw [he]
    exact hbF

/-- The all-original-label relative width condition in `DSide` is exactly
the per-source-frame condition of the raw constructor at gain four. -/
theorem source_frame_relative_width {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r) (i : ℕ)
    (hN : 0 < p.N k) {g : ℝ}
    (hrel : ∀ b : Fin a.C, a.lev b = i →
      g ≤ p.N k ^ (-4 : ℝ) * minorWidth (a.Q b) / (2 : ℝ) ^ a.T i)
    (e : Fin (sourceFrame a ha i).C) :
    g ≤ Pairing.minorWidth ((sourceFrame a ha i).Q e) /
      ((2 : ℝ) ^ (sourceFrame a ha i).T * p.N k ^ (4 : ℕ)) := by
  have he := hrel (a.layerEmb i e) (a.layerEmb_lev i e)
  rw [minorWidth_eq_pairing] at he
  have hscale : p.N k ^ (-4 : ℝ) = (p.N k ^ (4 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hN.le]
    norm_num
  rw [hscale] at he
  change g ≤ Pairing.minorWidth (a.Q (a.layerEmb i e)) /
    ((2 : ℝ) ^ a.T i * p.N k ^ (4 : ℕ))
  convert he using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end Submission.Obl.k4_raw_localized_native_systems.C
