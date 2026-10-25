-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.CoarseDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TerminalCount
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.MaximalDensity

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Two-dimensional ambient counts force a density-maximizing sublinear cell away
from the terminal scale. All exponent choices are left explicit. -/
lemma coarse_scale_of_density {δ r a b s η C N S Q : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hN : 0 < N) (hC : 0 ≤ C) (hs : 0 ≤ 2 - s)
    (hsmall : C * δ ^ (a * (2 - s) - η - b) < 1)
    (hdense : δ ^ b * N ≤ S) (hmax : S * r ^ s ≤ Q)
    (hcount : Q ≤ C * δ ^ (-η) * N * r ^ 2) : δ ^ a < r := by
  have hp : r ^ 2 = r ^ (2 - s) * r ^ s := by
    rw [← Real.rpow_add hr]
    have he : (2 : ℝ) - s + s = 2 := by ring
    rw [he, Real.rpow_two]
  have hh : δ ^ b * (N * r ^ s) ≤
      (C * δ ^ (-η) * r ^ (2 - s)) * (N * r ^ s) := by
    calc
      _ = (δ ^ b * N) * r ^ s := by ring
      _ ≤ S * r ^ s := mul_le_mul_of_nonneg_right hdense (Real.rpow_nonneg hr.le _)
      _ ≤ C * δ ^ (-η) * N * r ^ 2 := hmax.trans hcount
      _ = _ := by rw [hp]; ring
  have hd : δ ^ b ≤ C * δ ^ (-η) * r ^ (2 - s) :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < N * r ^ s)).mp hh
  by_contra hlate
  have hrδ : r ≤ δ ^ a := not_lt.mp hlate
  have he : C * δ ^ (-η) * (δ ^ a) ^ (2 - s) =
      (C * δ ^ (a * (2 - s) - η - b)) * δ ^ b := by
    rw [← Real.rpow_mul hδ.le, mul_assoc C, ← Real.rpow_add hδ,
      mul_assoc C, ← Real.rpow_add hδ]
    congr 2
    ring
  have hlt : δ ^ b < δ ^ b := by
    calc
      δ ^ b ≤ C * δ ^ (-η) * r ^ (2 - s) := hd
      _ ≤ C * δ ^ (-η) * (δ ^ a) ^ (2 - s) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hr.le hrδ hs) (by positivity)
      _ = (C * δ ^ (a * (2 - s) - η - b)) * δ ^ b := he
      _ < 1 * δ ^ b := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hδ _)
      _ = δ ^ b := one_mul _
  exact (lt_irrefl _ hlt)

/-- Every sufficiently populated root cell in a thin slope slice contains a coarse
sublinear Frostman class. This avoids a preliminary regularization of the hierarchy. -/
theorem exists_coarse_density_cell {η δ c a b s : ℝ} (hδ : 0 < δ)
    {n L : ℕ} (hn : 0 < n) (hL : 3 ≤ L)
    (x v : Fin n → Space) (U : Finset (Fin n))
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hthin : ∀ i ∈ U, |slope (v i) 0 - c| ≤ δ)
    (hroot : ∀ i ∈ U, ∀ i' ∈ U, dyadicLabel 3 (parameters (x i) (v i)) =
      dyadicLabel 3 (parameters (x i') (v i')))
    (hδL : δ ≤ ((2 : ℝ) ^ L)⁻¹) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hsmall : 2080000 * δ ^ (a * (2 - s) - η - b) < 1)
    (hdense : δ ^ b * (n : ℝ) ≤ U.card) :
    ∃ j, 3 ≤ j ∧ j ≤ L ∧ δ ^ a < ((2 : ℝ) ^ j)⁻¹ ∧ ∃ i₀ ∈ U,
      let Q := U.filter (fun i => dyadicLabel j (parameters (x i) (v i)) =
        dyadicLabel j (parameters (x i₀) (v i₀)))
      Q.Nonempty ∧ ∀ k, j ≤ k → k ≤ L → ∀ l : Fin 3 → ℤ,
        ((Q.filter (fun i => dyadicLabel k (parameters (x i) (v i)) = l)).card : ℝ) ≤
          (Q.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hU : U.Nonempty := Finset.card_pos.mp (by
    have hh : (0 : ℝ) < U.card := (mul_pos (Real.rpow_pos_of_pos hδ _) hnpos).trans_le hdense
    exact_mod_cast hh)
  obtain ⟨j, hj3, hjL, i₀, hi₀, hQ, hmax, hquotas⟩ :=
    maximal_dyadic_density_cell U hU (fun i => parameters (x i) (v i)) hL s hroot
  have hside : ((2 : ℝ) ^ j)⁻¹ ≤ 1 / 8 := by
    have hh : (2 : ℝ) ^ 3 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj3
    have hi := (inv_le_inv₀ (by positivity) (by positivity)).mpr hh
    norm_num at hi
    exact hi
  have hδj : δ ≤ ((2 : ℝ) ^ j)⁻¹ := hδL.trans
    ((inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) hjL))
  have hcount := thin_slice_dyadic_count hδ x v U hv htrans hball hF hthin hδj
    (by linarith : 5 * ((2 : ℝ) ^ j)⁻¹ ≤ 1)
    (dyadicLabel j (parameters (x i₀) (v i₀)))
  have hrootpow : (((2 : ℝ) ^ 3)⁻¹) ^ s ≤ 1 :=
    Real.rpow_le_one (by positivity) (by norm_num) hs
  have hmax' : (U.card : ℝ) * (((2 : ℝ) ^ j)⁻¹) ^ s ≤
      (U.filter (fun i => dyadicLabel j (parameters (x i) (v i)) =
        dyadicLabel j (parameters (x i₀) (v i₀)))).card :=
    hmax.trans ((mul_le_mul_of_nonneg_left hrootpow (Nat.cast_nonneg _)).trans_eq (mul_one _))
  have hcoarse := coarse_scale_of_density hδ (by positivity) hnpos (by norm_num)
    (by linarith : 0 ≤ 2 - s) hsmall hdense hmax' hcount
  exact ⟨j, hj3, hjL, hcoarse, i₀, hi₀, hQ,
    fun k hjk hkL l => hquotas k (hj3.trans hjk) hkL l⟩

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
