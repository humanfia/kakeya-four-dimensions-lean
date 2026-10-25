-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_family_improvement.FactorVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_family_improvement.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_concentrated_family_improvement

/-- A Katz--Tao estimate becomes a normalized Frostman estimate once its coefficient
is at most the total number of tubes times the area scale and the permitted error. -/
theorem frostman_of_katz_tao {δ c L : ℝ} {k : ℕ} {x v : Fin k → Space}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hc : c ≤ L * k * δ ^ 2)
    (hKT : ∀ U : Set Space, Convex ℝ U →
      o ((Set.ncard {i | T δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤ o c * μ U) :
    ∀ U : Set Space, Convex ℝ U →
      o (Set.ncard {i | T δ (x i) (v i) ⊆ U} : ℝ) ≤ o (L * k) * μ U := by
  intro U hU
  apply (ENNReal.mul_le_mul_iff_left
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hδ)) ENNReal.ofReal_ne_top).mp
  calc
    _ = o ((Set.ncard {i | T δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) := by
      exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ o c * μ U := hKT U hU
    _ ≤ o (L * k * δ ^ 2) * μ U :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _
    _ = (o (L * k) * μ U) * o (δ ^ 2) := by
      dsimp only [o]
      rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_right_comm _ _ _

/-- The failure of Frostman counting on every sufficiently large subfamily forces
any saturated factorization to consist of small-volume prisms. -/
theorem factorization_volume_bound {ν θ ζ δ a b m : ℝ} {n : ℕ}
    {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hνθ : ν ≤ θ) (hνζ : ν ≤ ζ / 2)
    (hfac : F ν δ a b m n x v) (hno : N θ ζ δ n x v) :
    a * b ≤ δ ^ (ζ / 2) := by
  obtain ⟨k, g, hg, hk, hlarge, c, hc1, hcm, hKT, q, hq, W,
    hshape, hcover, hmult, hbalance, hsat, habove, hbelow⟩ := hfac
  by_contra hvol
  have hvol' : δ ^ (ζ / 2) ≤ a * b := le_of_lt (lt_of_not_ge hvol)
  have hθlarge : δ ^ θ * n ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνθ) (Nat.cast_nonneg _)).trans hlarge
  apply hno k g hg hθlarge
  apply frostman_of_katz_tao hδ (Real.rpow_nonneg hδ.le _) _ hKT
  have hcount : (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W ⟨0, hq⟩} : ℝ) ≤ k := by
    exact_mod_cast (show
        Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W ⟨0, hq⟩} ≤ k from
      by simpa using Set.ncard_le_card {i | T δ (x (g i)) (v (g i)) ⊆ W ⟨0, hq⟩})
  have hsat' : δ ^ ν * c * (a * b) ≤ (k : ℝ) * δ ^ 2 := by
    calc
      _ = δ ^ ν * c * a * b := by ring
      _ ≤ _ := hsat ⟨0, hq⟩
      _ ≤ (k : ℝ) * δ ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
  have hc0 : 0 ≤ c := le_trans zero_le_one hc1
  have hpow : δ ^ ζ ≤ δ ^ (ν + ζ / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hscaled : δ ^ ζ * c ≤ (k : ℝ) * δ ^ 2 := by
    calc
      δ ^ ζ * c ≤ δ ^ (ν + ζ / 2) * c := mul_le_mul_of_nonneg_right hpow hc0
      _ = δ ^ ν * c * δ ^ (ζ / 2) := by rw [Real.rpow_add hδ]; ring
      _ ≤ δ ^ ν * c * (a * b) := mul_le_mul_of_nonneg_left hvol' (by positivity)
      _ ≤ _ := hsat'
  calc
    c = δ ^ (-ζ) * (δ ^ ζ * c) := by
      rw [← mul_assoc, ← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ δ ^ (-ζ) * ((k : ℝ) * δ ^ 2) :=
      mul_le_mul_of_nonneg_left hscaled (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-ζ) * k * δ ^ 2 := by ring

end WangZahlLot.Obl.wz_concentrated_family_improvement
