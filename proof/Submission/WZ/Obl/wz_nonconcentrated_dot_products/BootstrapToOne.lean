-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.BootstrapToOne.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.BootstrapIteration

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- A finite iteration followed by the base-scale loss upgrades the seed to
one-dimensional thin tubes, conditional on the supplied improvement step. -/
theorem thin_tube_bootstrap_to_one {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ C K c τ M ε β : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hτ : 0 < τ) (hM : 1 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : (4 : ℝ) ^ N * c < 1 / 10)
    (hreach : 1 - ε ≤ β + (N : ℝ) * τ)
    (hrange : ∀ n : ℕ, n < N → β + (n : ℝ) * τ ≤ 1 - ε)
    (hstep : ∀ σ L e : ℝ, β ≤ σ → σ ≤ 1 - ε → 1 ≤ L → 0 < e → e < 1 / 10 →
      SymmetricThinTubes δ σ L e f g →
      SymmetricThinTubes δ (σ + τ) ((C * L / e) ^ M) (4 * e) f g)
    (hseed : SymmetricThinTubes δ β K c f g) :
    SymmetricThinTubes δ 1
      (δ ^ (-ε) * (C * K / c) ^ ((2 * M) ^ N)) ((4 : ℝ) ^ N * c) f g := by
  have hc1 : c ≤ 1 := by
    have hp : 1 ≤ (4 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  have hB := (bootstrap_base_bounds hC hK hc hc1).1
  have hL : 1 ≤ (C * K / c) ^ ((2 * M) ^ N) := Real.one_le_rpow hB (by positivity)
  have hi := thin_tube_bootstrap_iterates hδ hC hK hc hτ hM hfinal hrange hstep hseed
  have hd := hi.decrease_exponent hδ hL (sub_nonneg.mpr hε1) hreach
  have hu := hd.increase_exponent hδ (zero_le_one.trans hL) (by linarith : 1 - ε ≤ 1)
  simpa only [sub_sub_cancel_left] using hu

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
