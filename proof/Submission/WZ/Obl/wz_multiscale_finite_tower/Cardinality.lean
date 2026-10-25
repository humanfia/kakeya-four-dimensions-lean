-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Cardinality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Products
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- A unit-tube shading has total mass bounded by the number of tubes times their volume. -/
lemma Admissible.mass_le {d η M L : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hA : Admissible d η M L n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    (∑ i, volume (Y i)) ≤ ENNReal.ofReal (384 * n * d ^ 2) := by
  calc
    (∑ i, volume (Y i)) ≤ ∑ _i : Fin n, ENNReal.ofReal (384 * d ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact (measure_mono (hA.2.1 i).2.2.2).trans
        (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hd hd1 (x i) (v i) (hA.2.1 i).1)
    _ = ENNReal.ofReal (n * (384 * d ^ 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = _ := by congr 1; ring

/-- Retaining a prescribed fraction of shading mass retains a quantitative number of tubes. -/
lemma retained_cardinality {d η η' ζ M L M' L' : ℝ} {n m : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    {x' v' : Fin m → Space} {Y' : Fin m → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hA : Admissible d η M L n x v Y) (hA' : Admissible d η' M' L' m x' v' Y')
    (hmass : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j)) :
    (1 / 384 : ℝ) * d ^ (η + ζ) * n ≤ m := by
  have h := ((mul_le_mul_of_nonneg_left hA.2.2.2.1 (by positivity)).trans hmass).trans
    (hA'.mass_le hd hd1)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have he : d ^ ζ * (d ^ η * n * d ^ 2) = (d ^ (η + ζ) * n) * d ^ 2 := by
    rw [Real.rpow_add hd]
    ring
  rw [he] at hr
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp hr
  linarith

lemma volumeFactor_eq {s N : ℝ} (hs : 0 < s) (hN : 0 < N) (σ ω : ℝ) :
    volumeFactor σ ω s N = N ^ (1 - σ) * s ^ (ω + 2 - σ) := by
  have hn : N * N ^ (-σ) = N ^ (1 - σ) := by
    calc
      _ = N ^ (1 : ℝ) * N ^ (-σ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN, sub_eq_add_neg]
  have hp : s ^ ω * s ^ 2 * s ^ (-σ) = s ^ (ω + 2 - σ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hs, ← Real.rpow_add hs, sub_eq_add_neg]
  dsimp [volumeFactor]
  rw [Real.mul_rpow hN.le hs.le]
  calc
    _ = (N * N ^ (-σ)) * (s ^ ω * s ^ 2 * s ^ (-σ)) := by ring
    _ = _ := by rw [hn, hp]

/-- The dependence on the family cardinality is increasing for sigma at most one. -/
lemma volumeFactor_mono_card {s N N' σ ω : ℝ} (hs : 0 < s)
    (hN : 0 < N) (hNN : N ≤ N') (hσ : σ ≤ 1) :
    volumeFactor σ ω s N ≤ volumeFactor σ ω s N' := by
  rw [volumeFactor_eq hs hN, volumeFactor_eq hs (hN.trans_le hNN)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hN.le hNN (by linarith)) (by positivity)

/-- A volume improvement transfers back through a cardinality loss, with an explicit exponent cost. -/
theorem VolumeBound.of_refinement {σ ω κ α d c ζ : ℝ} {n m : ℕ}
    {Y : Fin n → Set Space} {Y' : Fin m → Set Space}
    (hd : 0 < d) (hc : 0 < c) (hκ : 0 ≤ κ) (hn : 0 < n) (hσ : σ ≤ 1)
    (hcard : c * d ^ ζ * n ≤ m) (hsub : (⋃ j, Y' j) ⊆ (⋃ i, Y i))
    (hV : VolumeBound σ ω κ α d m Y') :
    VolumeBound σ ω (κ * c ^ (1 - σ)) (α - ζ * (1 - σ)) d n Y := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm' : 0 < (m : ℝ) := (by positivity : 0 < c * d ^ ζ * n).trans_le hcard
  have hcN := Real.rpow_le_rpow (by positivity : 0 ≤ c * d ^ ζ * n) hcard
    (show 0 ≤ 1 - σ by linarith)
  rw [Real.mul_rpow (by positivity : 0 ≤ c * d ^ ζ) hn'.le,
    Real.mul_rpow hc.le (Real.rpow_nonneg hd.le _), ← Real.rpow_mul hd.le] at hcN
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hV.trans (measure_mono hsub))
  have he (K a N : ℝ) : K * d ^ a * (N * d ^ 2) * (N * d) ^ (-σ) =
      K * volumeFactor σ a d N := by dsimp [volumeFactor]; ring
  rw [he, he, volumeFactor_eq hd hn', volumeFactor_eq hd hm']
  calc
    (κ * c ^ (1 - σ)) * ((n : ℝ) ^ (1 - σ) * d ^ (ω - (α - ζ * (1 - σ)) + 2 - σ)) =
        κ * (c ^ (1 - σ) * d ^ (ζ * (1 - σ)) * (n : ℝ) ^ (1 - σ)) *
          d ^ (ω - α + 2 - σ) := by
      rw [show ω - (α - ζ * (1 - σ)) + 2 - σ = ζ * (1 - σ) + (ω - α + 2 - σ) by ring,
        Real.rpow_add hd]
      ring
    _ ≤ κ * (m : ℝ) ^ (1 - σ) * d ^ (ω - α + 2 - σ) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
