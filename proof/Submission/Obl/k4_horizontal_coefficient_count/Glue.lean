import Submission.Obl.k4_horizontal_coefficient_count.Model
import Submission.Obl.k4_horizontal_coefficient_count.Statement

namespace Submission.Obl.k4_horizontal_coefficient_count

theorem statement_of_raw_engine (hraw : RawEngine) : Statement := by
  intro N K hN hlim hK d κ ℓ S U e₀ hd0 hd1 hκ0 hκ1 hℓ0 hS0 hS1 hU0 he0 hsubcrit hℓ
    α mα ν μ ρ π b P T n j A B c F hBasic hCaps hAtlas hNested
  let cfg : InputData α := ⟨N, K, d, κ, ℓ, S, U, e₀, ν, μ, ρ, π, b, P, T, n, j, A, B, c, F⟩
  have hcfg : Subcritical cfg := ⟨hN, hlim, hK, hd0, hd1, hκ0, hκ1, hℓ0, hS0, hS1,
    hU0, he0, hsubcrit, hℓ rfl, hBasic, hCaps, hAtlas, hNested⟩
  let sMax := min (U / 4) (e₀ / 200)
  obtain ⟨hs0, hsU, hse⟩ := canonical_buffer hU0 he0
  refine ⟨sMax, 2, hs0, hsU, hse, by norm_num, fun _ => rfl, ?_⟩
  intro u hu
  change u = 1 at hu
  subst u
  apply layers_of_heavy_covers N K hN hlim hK.1 hK.2 d e₀ 1 2 sMax ρ π b
    hcfg.residual_time hcfg.residual_floor hcfg.residual_mass_le
  intro s hs hsmax ε hε
  exact hraw α cfg hcfg s hs (by dsimp [sMax] at hsmax; linarith)
    (by dsimp [sMax] at hsmax; linarith) ε hε

end Submission.Obl.k4_horizontal_coefficient_count
