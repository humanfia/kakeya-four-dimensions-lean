-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.ReferenceGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyGain
import Submission.WZ.Obl.wz_multiscale_finite_tower.CertificateRetention

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

lemma AlignedFamily.retained_cardinality {d θ θ' ζ K L K' L' h h' : ℝ} {u u' : Space} {n m : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} {x' v' : Fin m → Space} {Z : Fin m → Set Space}
    (F : AlignedFamily d (d ^ θ) K L u h n x v Y)
    (F' : AlignedFamily d (d ^ θ') K' L' u' h' m x' v' Z)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hret : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    (1 / 56 : ℝ) * d ^ (θ + ζ) * n ≤ m := by
  have hh := ((mul_le_mul' le_rfl F.mass_lower).trans hret).trans (F'.mass_upper hd.le hd1)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le ζ)] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * (m : ℝ) * d ^ 2)).mp hh
  have he : d ^ ζ * (d ^ θ * n * d ^ 2) = (d ^ (θ + ζ) * n) * d ^ 2 := by
    rw [Real.rpow_add hd]
    ring
  rw [he] at hr
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp hr
  linarith

lemma volume_gain_card_transfer {d θ loss κ G σ ω : ℝ} {n m : ℕ} {E : Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (hG : 0 ≤ G)
    (hn : 0 < n) (hm : 0 < m) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hcard : (1 / 56 : ℝ) * d ^ θ * n ≤ m)
    (hvol : ENNReal.ofReal (κ * d ^ loss * volumeFactor σ ω d m * G) ≤ volume E) :
    ENNReal.ofReal ((κ / 56) * d ^ (loss + θ) * volumeFactor σ ω d n * G) ≤ volume E := by
  have hp : d ^ θ * d ^ (-θ) = 1 := by rw [← Real.rpow_add hd]; simp
  have hR : 1 ≤ 56 * d ^ (-θ) := by
    have hh : 1 ≤ d ^ (-θ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr hθ)
    linarith
  have hnm : (n : ℝ) ≤ (56 * d ^ (-θ)) * m := by
    have hh := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 56 * d ^ (-θ) by positivity)
    have he : (56 * d ^ (-θ)) * ((1 / 56 : ℝ) * d ^ θ * n) = (n : ℝ) := by
      rw [show (56 * d ^ (-θ)) * ((1 / 56 : ℝ) * d ^ θ * n) = (d ^ θ * d ^ (-θ)) * n by ring, hp, one_mul]
    rwa [he] at hh
  have hv := volumeFactor_card_loss (ω := ω) hd (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hm) hR hnm hσ hσ1
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
  calc
    _ ≤ (κ / 56) * d ^ (loss + θ) * ((56 * d ^ (-θ)) * volumeFactor σ ω d m) * G :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by positivity)) hG
    _ = _ := by
      rw [Real.rpow_add hd]
      have he : (κ / 56) * (d ^ loss * d ^ θ) * ((56 * d ^ (-θ)) * volumeFactor σ ω d m) * G =
          κ * d ^ loss * volumeFactor σ ω d m * G * (d ^ θ * d ^ (-θ)) := by ring
      rw [he, hp, mul_one]

theorem HierarchyAnalysis.gain_volume_bound {d θ g gap ζ σ ω c loss α h : ℝ}
    {J B k n : ℕ} {T : TubeHierarchy J} {Y : Fin n → Set Space}
    (H : HierarchyControl d θ g gap T) (A : HierarchyAnalysis T (⋃ i, Y i) d θ (d ^ ζ))
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hloss : 0 ≤ loss)
    (hc : 0 < c) (hc1 : c ≤ 1) (hα : 0 ≤ α) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hn : 0 < n) (hcard : (1 / 56 : ℝ) * d ^ θ * n ≤ (T.layer J).card)
    (hJB : J ≤ B) (hk : k < J)
    (hgap : (T.layer (k + 1)).radius / (T.layer k).radius ≤ d ^ h)
    (hbase : ∀ j, j < J → FibreVolumeBound A σ ω j (c * d ^ loss))
    (hgain : FibreVolumeBound A σ ω k
      (c * d ^ loss * ((T.layer (k + 1)).radius / (T.layer k).radius) ^ (-α))) :
    VolumeBound σ ω (((c / 256) ^ B) / 56)
      (h * α - (2 * θ + B * (ζ + 2 * θ + loss))) d n Y := by
  have ht : 0 < (T.layer (k + 1)).radius / (T.layer k).radius :=
    div_pos (H.positive (k + 1) (by omega)) (H.positive k hk.le)
  have hv := A.uniform_gain H hd hd1 hθ hζ hloss hc hc1 (Real.rpow_nonneg ht.le _) hσ hσ1 hJB hk hbase hgain
  have hv' := volume_gain_card_transfer hd hd1 hθ (by positivity : 0 ≤ (c / 256) ^ B)
    (Real.rpow_nonneg ht.le _) hn (T.layer J).card_pos hσ hσ1 hcard hv
  have hh := volume_bound_of_gap_gain hd ht (by positivity : 0 ≤ (c / 256) ^ B / 56) hα hgap hv'
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
