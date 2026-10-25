-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CertificateRetention.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.PreparedHierarchy
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertCertificate

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya

lemma AlignedFamily.mass_upper {d lam K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (F : AlignedFamily d lam K L u h n x v Y) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (∑ i, volume (Y i)) ≤ ENNReal.ofReal (56 * n * d ^ 2) := by
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (56 * d ^ 2) := Finset.sum_le_sum fun i _ =>
      (measure_mono (F.shading i)).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hd hd1 _ _ (F.unit i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

lemma AlignedFamily.mass_retention_of_card {d θ ε ell K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (F : AlignedFamily d (d ^ θ) K L u h n x v Y) (hd : 0 < d) (hd1 : d ≤ 1)
    (S : Finset (Fin n)) (hcard : d ^ ell * n ≤ S.card)
    (hcoef : 56 * d ^ ε ≤ d ^ (θ + ell)) :
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i) := by
  calc
    _ ≤ ENNReal.ofReal (d ^ ε) * ENNReal.ofReal (56 * n * d ^ 2) :=
      mul_le_mul' le_rfl (F.mass_upper hd.le hd1)
    _ = ENNReal.ofReal ((56 * d ^ ε) * n * d ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((d ^ (θ + ell)) * n * d ^ 2) := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)) (sq_nonneg d))
    _ ≤ ENNReal.ofReal (d ^ θ * S.card * d ^ 2) := ENNReal.ofReal_le_ofReal (by
      rw [Real.rpow_add hd, mul_assoc (d ^ θ) (d ^ ell)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hd.le _)) (sq_nonneg d))
    _ = ∑ _i ∈ S, ENNReal.ofReal (d ^ θ * d ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      congr 1
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => F.density i

lemma HierarchyControl.weaken_gap {d θ g gap gap' : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hd1 : d ≤ 1) (hgap : gap' ≤ gap) :
    HierarchyControl d θ g gap' T := by
  refine { H with upper_gap := ?_ }
  intro j hj
  exact (H.upper_gap j hj).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 hgap) (H.positive j hj.le).le)

lemma slab_coefficient_of_retention {lam A L K n m : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (hm : 0 ≤ m) (hret : lam * n ≤ A * m) (hcoef : L * A / lam ≤ K) : L * n ≤ K * m := by
  have hh := mul_le_mul_of_nonneg_left hret (div_nonneg hL hlam.le)
  have he : L / lam * (lam * n) = L * n := by field_simp
  rw [he] at hh
  calc
    L * n ≤ L / lam * (A * m) := hh
    _ = (L * A / lam) * m := by ring
    _ ≤ K * m := mul_le_mul_of_nonneg_right hcoef hm

end WangZahlLot.Obl.wz_multiscale_finite_tower
