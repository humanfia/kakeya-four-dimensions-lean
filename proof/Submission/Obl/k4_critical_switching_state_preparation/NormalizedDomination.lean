import Submission.Obl.k4_critical_switching_state_preparation.Transport
import Submission.Obl.k4_horizon_chart_assembly.TimeTransport

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The only Jacobian in time normalization is the original block length. -/
theorem map_normalizeTime_prod (m : Measure α) [SFinite m]
    (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    (m.prod volume).map (cfg.normalizeTime k s i) =
      ENNReal.ofReal (cfg.timeLength k s) • (m.prod volume) := by
  have heq : cfg.normalizeTime k s i =
      Submission.Obl.k4_horizon_chart_assembly.timeLift
        (-cfg.blockLeft k s i / cfg.timeLength k s) (cfg.timeLength k s)⁻¹ := by
    funext p
    apply Prod.ext
    · rfl
    · dsimp [normalizeTime, Submission.Obl.k4_horizon_chart_assembly.timeLift]
      ring
  rw [heq, Submission.Obl.k4_horizon_chart_assembly.map_timeLift_prod m _
    (inv_pos.mpr (cfg.timeLength_pos k s)), inv_inv]

/-- A source supported on its full original parent retains the original
trajectory prior through normalization, with density ceiling K times length. -/
theorem AssignmentLevel.normalized_source_domination (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (parent : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    (source : Set (α × ℝ)) (hsource : ∀ p ∈ source, p.1 ∈ cfg.A k s i) :
    ((cfg.ρ k).restrict source).map (cfg.normalizeTime k s i) ≤
      ENNReal.ofReal (cfg.K k * cfg.timeLength k s) •
        ((cfg.ν k).restrict (cfg.A k s i)).prod volume := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have hρ : cfg.ρ k ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume) :=
    (h.basic k).2.2.2.2.1.trans (h.basic k).2.2.2.1
  have hsub : source ⊆ cfg.A k s i ×ˢ (univ : Set ℝ) :=
    fun p hp => ⟨hsource p hp, mem_univ _⟩
  have hraw : (cfg.ρ k).restrict source ≤
      ENNReal.ofReal (cfg.K k) • ((cfg.ν k).restrict (cfg.A k s i)).prod volume := by
    calc
      _ ≤ (ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume)).restrict source :=
        Measure.restrict_mono_measure hρ source
      _ ≤ (ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume)).restrict
          (cfg.A k s i ×ˢ univ) := Measure.restrict_mono_set _ hsub
      _ = _ := by rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]
  have hmap := Measure.map_mono hraw (cfg.measurable_normalizeTime k s i)
  rwa [Measure.map_smul _ (cfg.measurable_normalizeTime k s i).aemeasurable,
    map_normalizeTime_prod, smul_smul, ← ENNReal.ofReal_mul hK] at hmap

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
