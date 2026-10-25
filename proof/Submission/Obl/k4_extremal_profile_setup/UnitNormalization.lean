import Submission.Obl.k4_extremal_profile_setup.BaseChange
import Submission.Obl.k4_extremal_profile_setup.Reindex
import Submission.Obl.k4_extremal_profile_setup.ScalarBridge

namespace Submission.Obl.k4_extremal_profile_setup

open Filter

/-- The exact problems may be normalized to length one.  The discarded initial
resolutions only increase the horizon, and all floors and angular parameters are
preserved by the fixed positive-power change of base.
-/
theorem unitNormalization (hi : InitialHorizon) : UnitNormalization := by
  intro S η p
  have hL := p.2.1.L_pos
  have ht : Tendsto (fun k => p.1.N k ^ p.1.L) atTop atTop :=
    (tendsto_rpow_atTop hL).comp p.2.1.2.1
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2))
  let φ : ℕ → ℕ := fun k => k₀ + k
  have hφ : StrictMono φ := fun i j hij => Nat.add_lt_add_left hij k₀
  let q₀ := p.1.reindex φ
  have hq₀ : q₀.Valid := p.2.1.reindex hφ.tendsto_atTop
  have hbase (k : ℕ) : 2 ≤ q₀.N k ^ p.1.L := hk₀ (φ k) (by dsimp [φ]; omega)
  let q := q₀.rebase p.1.L
  have hq : q.Valid := hq₀.rebase hL hbase
  refine ⟨⟨q, hq, p.2.2.1, p.2.2.2⟩, ?_, le_rfl, ?_⟩
  · exact div_self hL.ne'
  · have h₁ := div_le_div_of_nonneg_right
      (horizon_le_reindex hi p.2.1 hφ.tendsto_atTop) hL.le
    exact h₁.trans (horizon_div_le_rebase hi hq₀ hL hbase)

end Submission.Obl.k4_extremal_profile_setup
