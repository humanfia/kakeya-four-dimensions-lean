import Submission.Obl.k4_horizontal_wide_interval_return.Core.Comparison
import Submission.Obl.k4_horizontal_wide_interval_return.LongComparison

/-!
# Proof of `NativeComparison`

The full-strip comparison `projected_agree`, rewritten in the exact frozen form of x0896's
`NativeComparison` interface (o250 split draft).
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set Filter

theorem nativeComparison_holds : NativeComparison := by
  intro hTC N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hℓκ
    α _ ν μ ρ π b P T n j A B c F
  dsimp only
  intro hbasic hcaps hprep hnest hproj buffer hbuf
  let cfg : Data α := ⟨N, K, d, κ, ℓ, S, U, e₀, ν, μ, ρ, π, b, P, T, n, j, A, B, c, F⟩
  have hv : cfg.Valid := ⟨hN, hNt, hK.1, hK.2, hd, hd1, hκ, hκ1, hℓ,
    hS, hS1, hU, he₀, hℓκ rfl, hbasic, hcaps, hprep, hnest⟩
  obtain ⟨s₀, s, u, v, R, M, hdep, hag⟩ :=
    Core.projected_agree hTC cfg hv hproj hbuf
  refine ⟨s₀, s, u, v, R, hdep.s₀_pos, hdep.buf_U, hdep.buf_e, hdep.s₀_lt, hdep.u_pos,
    hdep.v_pos, hdep.v_lt_u, hdep.v_small, hdep.su_U, hdep.su_lt, hdep.wide_D, hdep.wide_h,
    hdep.R_gt, M, hdep.M_gt, hdep.M_U, hdep.M_e, fun ε hε => ?_⟩
  filter_upwards [hag ε hε] with k hk
  obtain ⟨L, hL⟩ := hk
  exact ⟨L.ρs, L.np, L.C, L.qp, L.G, L.le_rho, L.mass, L.cover, L.meas, L.disj, L.piece, L.sum, hL⟩

end Submission.Obl.k4_horizontal_wide_interval_return
