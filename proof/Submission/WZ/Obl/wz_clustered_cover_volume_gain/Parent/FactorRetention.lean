-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FactorRetention.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseFactorInput
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LocalizedFactorization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorEps

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open Finset MeasureTheory

/-- A fixed positive constant is absorbed by any prescribed negative power at small scales. -/
theorem fixed_constant_power_bound {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C ≤ δ ^ (-ν) := by
  refine ⟨C ^ (-(1 : ℝ) / ν), Real.rpow_pos_of_pos hC _, ?_⟩
  intro δ hδ hδd
  have he : (C ^ (-(1 : ℝ) / ν)) ^ (-ν) = C := by
    rw [← Real.rpow_mul hC.le]
    have hexp : (-(1 : ℝ) / ν) * (-ν) = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  rw [← he]
  exact Real.rpow_le_rpow_of_nonpos hδ hδd (by linarith)

/-- All errors in the assigned-box version of Proposition 4.6 fit in an arbitrarily
small power of the fine scale, uniformly for polynomially many coarse tubes. -/
theorem factor_assignment_power_bound {ν : ℝ} (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (N : ℕ) (ρ : ℝ), 0 < N → 0 < ρ → ρ ≤ 1 →
      (N : ℝ) / ρ ≤ δ ^ (-(6 : ℝ)) →
      2 * Factor.Kc 4 N ρ ^ 3 ≤ δ ^ (-ν) := by
  obtain ⟨C, hC, hK⟩ := Factor.Kc_le (ν / 36) (by positivity) 4 (by norm_num)
  obtain ⟨d, hd, hsmall⟩ := fixed_constant_power_bound
    (C := 2 * C ^ 3) (ν := ν / 2) (by positivity) (by positivity)
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd N ρ hN hρ hρ1 hsize
  have hbound : Factor.Kc 4 N ρ ≤ C * δ ^ (-(ν / 6)) := by
    refine (hK N hN ρ hρ hρ1).trans ?_
    have hp := Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) hρ.le) hsize
      (by positivity : 0 ≤ ν / 36)
    rw [← Real.rpow_mul hδ.le] at hp
    have he : -(6 : ℝ) * (ν / 36) = -(ν / 6) := by ring
    rw [he] at hp
    exact mul_le_mul_of_nonneg_left hp (by linarith)
  have hcube : Factor.Kc 4 N ρ ^ 3 ≤ C ^ 3 * δ ^ (-(ν / 2)) := by
    have hp := pow_le_pow_left₀ (Factor.Kc_pos (by norm_num : (0 : ℝ) < 4) N ρ).le
      hbound 3
    rw [mul_pow, ← Real.rpow_mul_natCast hδ.le] at hp
    have he : -(ν / 6) * (3 : ℕ) = -(ν / 2) := by push_cast; ring
    rwa [he] at hp
  calc
    2 * Factor.Kc 4 N ρ ^ 3 ≤ 2 * C ^ 3 * δ ^ (-(ν / 2)) := by linarith
    _ ≤ δ ^ (-(ν / 2)) * δ ^ (-(ν / 2)) :=
      mul_le_mul_of_nonneg_right (hsmall δ hδ hδd) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-ν) := by rw [← Real.rpow_add hδ]; congr 1; ring

namespace Interfaces

/-- Cardinality retention in a comparable coarse subcover retains complete fine fibers
with precisely the additional comparability and cardinality exponents. -/
theorem c_mass_retention_of_card_retention {δ η m l h ρ τ ε β : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (Q U : Finset (Fin N)) (hU : U.Nonempty) (hUQ : U ⊆ Q)
    (hkeep : o (δ ^ τ) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S with f i ∈ Q, μ (Z i))
    (hcmp : ∀ j ∈ Q, ∀ k ∈ Q,
      coarseWeight S Z f j ≤ δ ^ (-ε) * coarseWeight S Z f k)
    (hcard : (Q.card : ℝ) ≤ δ ^ (-β) * U.card) :
    o (δ ^ (τ + ε + β)) * ∑ i ∈ S, μ (Z i) ≤
      ∑ i ∈ S with f i ∈ U, μ (Z i) := by
  classical
  have hmass := comparable_mass_of_card_retention Q U (coarseWeight S Z f) hU hUQ
    (Real.rpow_nonneg hδ.le (-ε)) (Real.rpow_nonneg hδ.le (-β))
    (fun k _ => coarseWeight_nonneg S Z f k) hcmp hcard
  have hkeepR := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i _ => c_subshading_ne_top hA hC i)) hkeep
  simp only [o, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
    ENNReal.toReal_sum (fun i _ => c_subshading_ne_top hA hC i)] at hkeepR
  rw [← sum_coarseWeight S Z f Q, ← sum_coarseWeight_univ] at hkeepR
  have hcancel : δ ^ (ε + β) * (δ ^ (-ε) * δ ^ (-β)) = 1 := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    rw [show ε + β + (-ε + -β) = 0 by ring, Real.rpow_zero]
  have hreal : δ ^ (τ + ε + β) * ∑ k, coarseWeight S Z f k ≤
      ∑ k ∈ U, coarseWeight S Z f k := by
    calc
      _ = δ ^ (ε + β) * (δ ^ τ * ∑ k, coarseWeight S Z f k) := by
        rw [← mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ δ ^ (ε + β) * (δ ^ (-ε) * δ ^ (-β) * ∑ k ∈ U, coarseWeight S Z f k) :=
        mul_le_mul_of_nonneg_left (hkeepR.trans hmass) (Real.rpow_nonneg hδ.le _)
      _ = _ := by rw [← mul_assoc, hcancel, one_mul]
  have ho := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)] at ho
  change o (δ ^ (τ + ε + β)) * o (∑ k, coarseWeight S Z f k) ≤
    o (∑ k ∈ U, coarseWeight S Z f k) at ho
  rw [ofReal_sum_coarseWeight hA hC U] at ho
  have hall : o (∑ k, coarseWeight S Z f k) = ∑ i ∈ S, μ (Z i) := by
    simpa using ofReal_sum_coarseWeight hA hC (Finset.univ : Finset (Fin N))
  rwa [hall] at ho

/-- The corrected gain hypothesis forces every retained factored subcover to have a
large Katz--Tao coefficient. This uses mass retention, rather than the original cover. -/
theorem large_coefficient_of_no_small_retained_cover {δ η m l h ρ τ ε β ζ M : ℝ}
    {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbudget : τ + ε + β ≤ ζ / 2)
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (Q U : Finset (Fin N)) (hU : U.Nonempty) (hUQ : U ⊆ Q)
    (hkeep : o (δ ^ τ) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S with f i ∈ Q, μ (Z i))
    (hcmp : ∀ j ∈ Q, ∀ k ∈ Q,
      coarseWeight S Z f j ≤ δ ^ (-ε) * coarseWeight S Z f k)
    (hcard : (Q.card : ℝ) ≤ δ ^ (-β) * U.card)
    (hK : ∀ W, Convex ℝ W →
      o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o M * μ W)
    (hno : ∀ U : Finset (Fin N),
      o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S with f i ∈ U, μ (Z i) →
      ¬ ∀ W, Convex ℝ W →
        o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) :
    δ ^ (-ζ) < M := by
  have hretain := c_mass_retention_of_card_retention hδ hA hC Q U hU hUQ hkeep hcmp hcard
  have hretain' : o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤
      ∑ i ∈ S with f i ∈ U, μ (Z i) := by
    refine le_trans ?_ hretain
    apply mul_le_mul_left
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget)
  by_contra hlarge
  have hM : M ≤ δ ^ (-ζ) := le_of_not_gt hlarge
  apply hno U hretain'
  intro W hW
  exact (hK W hW).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hM) _)

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
