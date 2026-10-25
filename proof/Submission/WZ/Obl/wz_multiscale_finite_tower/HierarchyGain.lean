-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyProduct

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya

lemma FibreVolumeBound.mono {d θ g gap ρ σ ω K K' : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {E : Set Space} {A : HierarchyAnalysis T E d θ ρ}
    {j : ℕ} (hj : j < J) (hK : K ≤ K') (h : FibreVolumeBound A σ ω j K') :
    FibreVolumeBound A σ ω j K := by
  obtain ⟨k, m, e, hm, hep, hc, hv⟩ := h
  have hr := H.positive j hj.le
  have hs := H.positive (j + 1) (by omega)
  have hfac : 0 ≤ (T.layer j).radius ^ 2 *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m := by
    dsimp [volumeFactor]
    positivity
  refine ⟨k, m, e, hm, hep, hc, (ENNReal.ofReal_le_ofReal ?_).trans hv⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hK hfac

/-- A single exceptional edge improves the entire product. The coefficient and
loss depend only on the allowed number of levels. -/
theorem HierarchyAnalysis.uniform_gain {d θ g gap ζ σ ω c loss G : ℝ}
    {J B k : ℕ} {T : TubeHierarchy J} (H : HierarchyControl d θ g gap T)
    {E : Set Space} (A : HierarchyAnalysis T E d θ (d ^ ζ))
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hloss : 0 ≤ loss)
    (hc : 0 < c) (hc1 : c ≤ 1) (hG : 0 ≤ G) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hJB : J ≤ B) (hk : k < J)
    (hbase : ∀ j, j < J → FibreVolumeBound A σ ω j (c * d ^ loss))
    (hgain : FibreVolumeBound A σ ω k (c * d ^ loss * G)) :
    ENNReal.ofReal ((c / 256) ^ B * d ^ (θ + B * (ζ + 2 * θ + loss)) *
      volumeFactor σ ω d (T.layer J).card * G) ≤ volume E := by
  classical
  let K : ℕ → ℝ := fun j => c * d ^ loss * if j = k then G else 1
  have hK (j) (hj : j < J) : 0 ≤ K j := by
    dsimp only [K]
    split_ifs <;> positivity
  have hlocal (j) (hj : j < J) : FibreVolumeBound A σ ω j (K j) := by
    by_cases he : j = k
    · subst j
      simpa [K] using hgain
    · simpa only [K, if_neg he, mul_one] using hbase j hj
  have hv := A.volume_product H hd hd1 hθ (Real.rpow_nonneg hd.le ζ) hσ hσ1 K hK hlocal
  have hprod : (∏ j ∈ Finset.range J, K j) = (c * d ^ loss) ^ J * G := by
    dsimp only [K]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    simp [hk]
  rw [hprod] at hv
  have he : d ^ θ * (d ^ ζ / 256 * d ^ (2 * θ)) ^ J * ((c * d ^ loss) ^ J * G) *
      volumeFactor σ ω d (T.layer J).card =
      (c / 256) ^ J * d ^ (θ + J * (ζ + 2 * θ + loss)) *
        volumeFactor σ ω d (T.layer J).card * G := by
    rw [Real.rpow_add hd,
      show (J : ℝ) * (ζ + 2 * θ + loss) = (ζ + 2 * θ + loss) * J by ring,
      Real.rpow_mul_natCast hd.le]
    have hp : d ^ (ζ + 2 * θ + loss) = d ^ ζ * d ^ (2 * θ) * d ^ loss := by
      rw [Real.rpow_add hd, Real.rpow_add hd]
    rw [hp]
    simp only [mul_pow, div_pow]
    ring
  rw [he] at hv
  have hc256 : 0 ≤ c / 256 := by positivity
  have hc2561 : c / 256 ≤ 1 := by linarith
  have hp : (c / 256) ^ B ≤ (c / 256) ^ J :=
    pow_le_pow_of_le_one hc256 hc2561 hJB
  have he' : θ + J * (ζ + 2 * θ + loss) ≤ θ + B * (ζ + 2 * θ + loss) := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hJB)
      (show 0 ≤ ζ + 2 * θ + loss by linarith)
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_ge hd hd1 he'
  have hfac : 0 ≤ volumeFactor σ ω d (T.layer J).card := by dsimp [volumeFactor]; positivity
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hv
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hp hpow (Real.rpow_nonneg hd.le _)
      (pow_nonneg hc256 _)) hfac) hG

end WangZahlLot.Obl.wz_multiscale_finite_tower
