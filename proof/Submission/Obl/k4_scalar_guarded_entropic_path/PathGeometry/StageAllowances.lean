import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StagePath
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FiniteViewBudgets
import Submission.Obl.k4_scalar_guarded_entropic_path.CommonGuard

/-! Original formats and guard complexities are fixed first. A single
small positive power allowance then works for every actual stage view. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Filter PathMeasures
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

structure StageAllowances (s : StagePath ctx source k R δ) where
  M₀ : ℕ
  M_one : 1 ≤ M₀
  formats : ∀ a, (s.views a).complexity ≤ M₀ ∧ M (s.views a).parent ≤ M₀ ∧
    D (s.views a).parent ≤ M₀ ∧ L (s.views a).parent ≤ (M₀ : ℝ)
  v : ℝ
  v_pos : 0 < v
  v_one : v ≤ 1
  v_scale : v < s.layout.scale / 100000
  power_budget : ((k + 1 : ℕ) : ℝ) * v < s.layout.scale * δ / 100
  guard : ∀ᶠ j in atTop, ∀ a r h, 0 ≤ r → r < L (s.views a).parent →
    h ≤ ctx.κ * r - s.layout.scale * δ / 1000 →
    ¬Chart (s.views a).parent (2 ^ ((M₀ + k + 1) ^ 2)) r (L (s.views a).parent) h
      (Real.log ((N s.final j ^ v * Real.log (N s.final j)) ^ (k + 1)) /
        Real.log (N s.final j)) false ((s.views a).suffixChain.sample j)

theorem nonempty_stageAllowances (s : StagePath ctx source k R δ) (hκ : 0 < ctx.κ) :
    Nonempty (StageAllowances s) := by
  obtain ⟨M₀, hM, hformats⟩ := exists_common_view_budget s.views
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hn : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  let θ := min (1 / 2 : ℝ) (min (s.layout.scale / 100000)
    ((s.layout.scale * δ / 100) / ((k + 1 : ℕ) : ℝ)))
  have hθ : 0 < θ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hknown : ∀ a r h, 0 ≤ r → r < Code.L (s.views a).parent →
      Known (s.views a).parent r (Code.L (s.views a).parent) h →
        ctx.κ * r - (s.layout.scale * δ / 1000) / 4 < h := by
    intro a r h hr hrL hh
    exact (s.controls a.val).known_lower r h hr hrL hh
  obtain ⟨v, hv, hvθ, hguard⟩ := exists_common_power_allowance_guard
    (fun a => (s.views a).parent) (fun a => (s.views a).parent_exact)
    (fun a => (s.views a).suffixChain.sample) (fun a => (s.views a).suffixChain.sample_strictMono)
    (N s.final) s.final_exact.1.2.1 hκ (by positivity : 0 < s.layout.scale * δ / 1000) hθ
    hknown (fun _ => 2 ^ ((M₀ + k + 1) ^ 2))
    (fun _ => one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) (k + 1) (Nat.succ_pos k)
  have hvhalf : v < 1 / 2 := hvθ.trans_le (min_le_left _ _)
  have hvscale : v < s.layout.scale / 100000 :=
    hvθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hvbudget : ((k + 1 : ℕ) : ℝ) * v < s.layout.scale * δ / 100 := by
    have hbound : v < (s.layout.scale * δ / 100) / ((k + 1 : ℕ) : ℝ) :=
      hvθ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have ht := (lt_div_iff₀ hn).mp hbound
    nlinarith only [ht]
  exact ⟨⟨M₀, hM, hformats, v, hv, by linarith, hvscale, hvbudget, hguard⟩⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
