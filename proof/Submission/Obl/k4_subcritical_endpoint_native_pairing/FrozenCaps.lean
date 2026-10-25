import Submission.Obl.k4_subcritical_endpoint_native_pairing.Model
import Submission.Obl.k4_subcritical_endpoint_native_pairing.PhysicalBase
import Submission.Obl.k4_horizontal_coefficient_count.LMExtract

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original joint caps at one fixed base resolution and velocity width,
uniformly over every larger hidden width. No new palette or law is introduced. -/
theorem Prepared.eventually_original_joint_caps (h : cfg.Prepared)
    {r M : ℝ} (hr : 0 < r) (hM : 0 < M) :
    ∀ᶠ k in atTop, ∀ w : ℝ, cfg.N k ^ (-r) ≤ w → w ≤ 1 →
      ∀ (c : Fin 3 → ℤ) (a v : ℤ),
      cfg.μ k {p | (fun e => ⌊parameterPhysicalBase (cfg.b k) p e /
        (cfg.N k ^ (-r))⌋) = c ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / w⌋ = a ∧
        ⌊cfg.b k p.1 3 / (cfg.N k ^ (-M))⌋ = v} ≤
        ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ 3 * w ^ cfg.d) *
          cfg.π k {v' | ⌊v' / (cfg.N k ^ (-M))⌋ = v} := by
  let R := 2 + r + r⁻¹ + M + M⁻¹
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM
  have hR : 1 < R := by dsimp [R]; linarith
  have hRp : 0 < R := by linarith
  have hrlo : R⁻¹ ≤ r := (inv_le_comm₀ hRp hr).mpr (by dsimp [R]; linarith)
  have hMlo : R⁻¹ ≤ M := (inv_le_comm₀ hRp hM).mpr (by dsimp [R]; linarith)
  have hrhi : r ≤ R := by dsimp [R]; linarith
  have hMhi : M ≤ R := by dsimp [R]; linarith
  filter_upwards [h.caps R hR] with k hk
  have hN : 1 < cfg.N k := by linarith [h.scale k]
  have hcoord : ∀ s : ℝ, 0 ≤ s → s ≤ r → ∀ n0 n1 n2 a v : ℤ,
      cfg.μ k {p | (⌊p.2 / cfg.N k ^ (-r)⌋ = n0 ∧
        ⌊Submission.Obl.k4_horizontal_coefficient_count.X1 (cfg.b k p.1) p.2 /
          cfg.N k ^ (-r)⌋ = n1 ∧
        ⌊Submission.Obl.k4_horizontal_coefficient_count.X2 (cfg.b k p.1) p.2 /
          cfg.N k ^ (-r)⌋ = n2) ∧
        ⌊Submission.Obl.k4_horizontal_coefficient_count.X3 (cfg.b k p.1) p.2 /
          cfg.N k ^ (-s)⌋ = a ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋ = v} ≤
        ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s)) *
          cfg.π k {v' | ⌊v' / cfg.N k ^ (-M)⌋ = v} := by
    intro s hs hsr n0 n1 n2 a v
    have hc := (hk r s M hrlo hrhi hs (hsr.trans hrhi) hMlo hMhi).2.2
      false ![n0, n1, n2] a v
    apply (measure_mono ?_).trans hc
    intro p hp
    refine ⟨?_, hp.2.1, hp.2.2⟩
    funext e
    fin_cases e
    · exact hp.1.1
    · exact hp.1.2.1
    · exact hp.1.2.2
  have hc := Submission.Obl.k4_horizontal_coefficient_count.capB_of hN hcoord
  intro w hw hw1 c a v
  have hbound := hc w hw hw1 (c 0) (c 1) (c 2) a v
  apply (measure_mono ?_).trans hbound
  intro p hp
  refine ⟨?_, ?_, ?_, hp.2.1, hp.2.2⟩
  · exact congrFun hp.1 0
  · exact congrFun hp.1 1
  · exact congrFun hp.1 2

end Data
end
end Submission.Obl.k4_subcritical_endpoint_native_pairing
