import Submission.Obl.k4_critical_switching_state_preparation.JointSource
import Submission.Obl.k4_critical_switching_state_preparation.SwitchingModel

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The exact occupied-pair source at the frozen critical gain. The exponent is
chosen before the sample, parent and affine primitive. Both the upper-count
child and a fine true history are retained with unchanged original mass. -/
theorem Valid.exists_critical_pair_source_exponent (h : cfg.Valid) {s δ : ℝ}
    (hs : 0 < s) (hsU : 1000 * s < cfg.U) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ s / 100 ∧
      ∀ᶠ k in atTop, ∀ (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ),
        L 0 = 0 → (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s) →
        Nonempty (cfg.RegularPairSource k s (s / 16) η δ
          {s + s / 16, 500 * s} i L) := by
  classical
  let η := min δ (s / 100)
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηs : η ≤ s / 100 := min_le_right _ _
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  refine ⟨η, hη, min_le_left _ _, hηs, ?_⟩
  apply h.eventually_regular_pair_source hs (by positivity) (by linarith)
    (by linarith) hη (by linarith) (by rw [hκ]; linarith) hδ
    {s + s / 16, 500 * s} (by simp)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> constructor <;> linarith

/-- Exact identification of a pair code after normalizing time. In particular,
normalization does not replace the original midpoint intercept bin. -/
theorem sourcePair_normalized_time (k : ℕ) (s v : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (ω : ℝ) (p : α × ℝ) :
    cfg.sourcePair k s i L (cfg.N k ^ (-s - v)) ω
      (p.1, cfg.blockLeft k s i + cfg.timeLength k s * p.2) =
      (cfg.midpointBin k s v i L p.1,
        fun e => ⌊cfg.centeredLine k s i p.1 p.2 e / ω⌋) := rfl

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
