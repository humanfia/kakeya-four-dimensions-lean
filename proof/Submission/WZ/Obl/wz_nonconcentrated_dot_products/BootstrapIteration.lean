-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.BootstrapIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinTubes
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.BootstrapConstants

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- Iteration of an assumed one-step thin-tube improvement. No improvement
theorem is asserted here: it is an explicit premise. -/
theorem thin_tube_bootstrap_iterates {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ C K c τ M t β : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hC : 1 ≤ C) (hK : 1 ≤ K) (hc : 0 < c)
    (hτ : 0 < τ) (hM : 1 ≤ M) (hfinal : (4 : ℝ) ^ N * c < 1 / 10)
    (hrange : ∀ n : ℕ, n < N → β + (n : ℝ) * τ ≤ t)
    (hstep : ∀ σ L e : ℝ, β ≤ σ → σ ≤ t → 1 ≤ L → 0 < e → e < 1 / 10 →
      SymmetricThinTubes δ σ L e f g →
      SymmetricThinTubes δ (σ + τ) ((C * L / e) ^ M) (4 * e) f g)
    (hseed : SymmetricThinTubes δ β K c f g) :
    SymmetricThinTubes δ (β + (N : ℝ) * τ)
      ((C * K / c) ^ ((2 * M) ^ N)) ((4 : ℝ) ^ N * c) f g := by
  let B := C * K / c
  have hc1 : c ≤ 1 := by
    have hp : 1 ≤ (4 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨hB, hKB, hCB⟩ := bootstrap_base_bounds hC hK hc hc1
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hL (n : ℕ) : 1 ≤ B ^ ((2 * M) ^ n) :=
    Real.one_le_rpow hB (by positivity)
  have hprev : ∀ n : ℕ, n ≤ N → SymmetricThinTubes δ (β + (n : ℝ) * τ)
      (B ^ ((2 * M) ^ n)) ((4 : ℝ) ^ n * c) f g := by
    intro n hn
    induction n with
    | zero =>
        simpa only [Nat.cast_zero, zero_mul, add_zero, pow_zero, Real.rpow_one, one_mul] using
          hseed.mono_constant hδ.le hKB
    | succ n ih =>
        have hnN : n < N := Nat.lt_of_succ_le hn
        have hthin := ih (Nat.le_of_lt hnN)
        have hcp : c ≤ (4 : ℝ) ^ n * c := by
          have hp : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          nlinarith
        have hcn : (4 : ℝ) ^ n * c < 1 / 10 := by
          have hp : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hnN)
          exact (mul_le_mul_of_nonneg_right hp hc.le).trans_lt hfinal
        have hσ : β ≤ β + (n : ℝ) * τ := by
          have hp : 0 ≤ (n : ℝ) * τ := by positivity
          linarith
        have hnext := hstep _ _ _ hσ (hrange n hnN) (hL n) (by positivity) hcn hthin
        have hcost := bootstrap_constant_step hB (zero_le_one.trans hC) hc hcp hM hCB n
        have hnext' := hnext.mono_constant hδ.le hcost
        convert hnext' using 1 <;> push_cast <;> (try simp only [pow_succ]) <;> ring
  exact hprev N le_rfl

/-- A finite number of uniform positive improvements reaches any fixed
target exponent. The number is chosen independently of the finite sets. -/
theorem exists_bootstrap_depth {τ t β : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, t ≤ β + (N : ℝ) * τ ∧
      ∀ n : ℕ, n < N → β + (n : ℝ) * τ < t := by
  have hex : ∃ N : ℕ, t ≤ β + (N : ℝ) * τ := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - β) / τ)
    have hh := (div_lt_iff₀ hτ).mp hN
    exact ⟨N, by linarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro n hn
  exact lt_of_not_ge (Nat.find_min hex hn)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
