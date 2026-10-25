import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Sample
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Eventually

/-!
# Conservativity: the field certificate carries a potential

`conservativity_contract` proves `ConservativityContract`: the Cartesian
field certificate of o231 upgrades, packet by packet and with the same data,
to one that also carries a bounded polynomial potential `P` and a bounded
measurable intercept `c` with `|X_l(t) - P(u_l(t)) - c(l)| ≤ H' N^(-1-2c*)`
throughout the block. The proof is the paper's switched-line argument
(Section 6, "Switched lines force approximate conservativity" and "A
potential"): `Cons/BlockCurl.lean` bounds the curl of the field on one block
from the actual four-switch path law, `Cons/BlockPotential.lean` integrates
the field, and `Cons/Sample.lean` makes the parameter choices at one sample.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Filter

theorem conservativity_contract : ConservativityContract := by
  intro N hN2 hNtop d κ S hd0 hd1 hκ0 hκ1 hS W ν ρ π T n γ j A H D Z B hH hZ hB hF
  obtain ⟨Cbig, hCbig, mbig, hsample⟩ := exists_sample_potential D
  refine ⟨fun k => Cbig * H k ^ mbig, D + 2,
    subpower_const_mul_pow hN2 hNtop hH Cbig hCbig mbig, ?_⟩
  intro R hR
  have hb : 0 < κ * (1 - d) / 64 := by
    have : 0 < 1 - d := by linarith
    positivity
  set R' := max R (max (Z + 1) (1 / (κ * (1 - d) / 64))) with hR'def
  have hR' : 1 < R' := lt_of_lt_of_le hR (le_max_left _ _)
  have hη : 0 < min (S * (κ * (1 - d) / 64)) (κ * (1 - d) / 1000) := by
    have : 0 < 1 - d := by linarith
    exact lt_min (mul_pos hS hb) (by positivity)
  filter_upwards [hF R' hR', eventually_mul_pow_le hN2 hNtop hH Cbig mbig hη] with k hk hbig
  obtain ⟨i, μ, z₀, 𝒯, hfield⟩ := hk
  have hR'b : R'⁻¹ ≤ κ * (1 - d) / 64 := by
    have h1 : 1 / (κ * (1 - d) / 64) ≤ R' := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [inv_le_comm₀ (by linarith) hb]
    simpa [one_div] using h1
  have hR'Z : Z + 1 ≤ R' := le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨P, c, hpot⟩ := hsample (N k) (H k) d κ S Z B R' (ν k (γ k 1 i)) (π k (γ k 1 i))
    (ρ k (γ k 1 i)) (A k 1 i) (T k 1) (j k 1 i) μ z₀ 𝒯 hfield (hN2 k) (hH.1 k) hd0 hd1 hκ0 hκ1
    hS hZ hB hR'b hR'Z hbig
  exact ⟨i, μ, z₀, 𝒯, P, c, hfield.mono (by linarith) (le_max_left _ _), hpot⟩

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
