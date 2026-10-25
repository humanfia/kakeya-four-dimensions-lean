-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.SplitScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedCertificate

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

lemma normalized_scale_span {d t c C : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hdt : d ≤ t) (ht1 : t ≤ 1) (hc : 0 ≤ c) (hC : 0 < C) (hsmall : C ^ 2 * d ≤ 1) :
    (C * t ^ c) / (t ^ (1 - c) / C) ≤ d ^ (-2 : ℝ) := by
  have hCbound : C ^ 2 ≤ d⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hd).mpr hsmall
  have hp : t ^ (2 * c - 1) ≤ t ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hp' : t ^ (-1 : ℝ) ≤ d ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos hd hdt (by norm_num)
  calc
    (C * t ^ c) / (t ^ (1 - c) / C) = C ^ 2 * t ^ (2 * c - 1) := by
      have he : t ^ (2 * c - 1) = t ^ c / t ^ (1 - c) := by
        rw [← Real.rpow_sub ht]
        congr 1
        ring
      rw [he]
      field_simp
      <;> ring
    _ ≤ C ^ 2 * d ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left (hp.trans hp') (sq_nonneg C)
    _ ≤ d⁻¹ * d ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg hd.le _)
    _ = d ^ (-2 : ℝ) := by rw [← Real.rpow_neg_one, ← Real.rpow_add hd]; norm_num

lemma normalized_split_scales {d t c C g h g' gap' u : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (ht : 0 < t) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hC : 1 ≤ C) (hgap : 0 ≤ gap')
    (htlo : d ^ g ≤ t) (hthi : t ≤ d ^ h)
    (hmesh : 1024 * C * d ^ g' ≤ d ^ ((1 - c) * g))
    (hsmall : 65536 * C * d ^ (c * h) ≤ d ^ gap')
    (hulo : 1024 * (t ^ (1 - c) / C) ≤ u) (huhi : u ≤ 1024 * (C * t ^ c)) :
    t ≤ t ^ (1 - c) / C ∧ C * t ^ c ≤ 1 / 65536 ∧
      0 < u ∧ u ≤ 1 / 64 ∧ d ^ g' ≤ u ∧ d ^ g' * u ≤ t ∧
      u ≤ d ^ gap' ∧ t ≤ d ^ gap' * u := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc0 : 0 ≤ 1 - c := by linarith
  have hlo : d ^ ((1 - c) * g) ≤ t ^ (1 - c) := by
    rw [mul_comm (1 - c) g, Real.rpow_mul hd.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hd.le _) htlo hc0
  have hhi : t ^ c ≤ d ^ (c * h) := by
    rw [mul_comm c h, Real.rpow_mul hd.le]
    exact Real.rpow_le_rpow ht.le hthi hc
  have hprod : t ^ (1 - c) * t ^ c = t := by rw [← Real.rpow_add ht]; norm_num
  have hprodC : t ^ (1 - c) * (C * t ^ c) = C * t := by
    rw [← mul_assoc, mul_comm (t ^ (1 - c)) C, mul_assoc, hprod]
  have htop : d ^ gap' ≤ 1 := Real.rpow_le_one hd.le hd1 hgap
  have hCt : 65536 * (C * t ^ c) ≤ d ^ gap' := by
    have hh := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 65536 * C by positivity)
    nlinarith only [hh, hsmall]
  have hCt1 : C * t ^ c ≤ 1 := by linarith
  have hApos : 0 < t ^ (1 - c) := Real.rpow_pos_of_pos ht _
  have htcpos : 0 < t ^ c := Real.rpow_pos_of_pos ht _
  have hraw : t ≤ t ^ (1 - c) / C := by
    apply (le_div_iff₀ hC0).mpr
    have hh := mul_le_mul_of_nonneg_left hCt1 hApos.le
    rw [hprodC, mul_one] at hh
    simpa only [mul_comm] using hh
  have hu0 : 0 < u := (mul_pos (by norm_num) (div_pos hApos hC0)).trans_le hulo
  have husmall : u ≤ d ^ gap' / 64 := by linarith
  have humesh : d ^ g' ≤ u := by
    have hh : C * d ^ g' ≤ t ^ (1 - c) := by
      have h0 : 0 < d ^ g' := Real.rpow_pos_of_pos hd _
      nlinarith only [hmesh, hlo, mul_pos hC0 h0]
    have hh' : d ^ g' ≤ t ^ (1 - c) / C := (le_div_iff₀ hC0).mpr (by nlinarith only [hh])
    linarith [div_pos hApos hC0]
  have hlmesh : d ^ g' * u ≤ t := by
    calc
      _ ≤ d ^ g' * (1024 * (C * t ^ c)) := mul_le_mul_of_nonneg_left huhi (Real.rpow_nonneg hd.le _)
      _ = (1024 * C * d ^ g') * t ^ c := by ring
      _ ≤ t ^ (1 - c) * t ^ c := mul_le_mul_of_nonneg_right (hmesh.trans hlo) htcpos.le
      _ = t := hprod
  have hlutop : t ≤ d ^ gap' * u := by
    have hCt' : C * t ^ c ≤ d ^ gap' := by linarith [mul_pos hC0 htcpos]
    have hmul := mul_le_mul_of_nonneg_left hCt' hApos.le
    rw [hprodC] at hmul
    have hulow : t ^ (1 - c) / C ≤ u := by linarith [div_pos hApos hC0]
    have hmul' := mul_le_mul_of_nonneg_left hulow (Real.rpow_nonneg hd.le gap')
    have hfirst : t ≤ d ^ gap' * (t ^ (1 - c) / C) := by
      apply (mul_le_mul_iff_left₀ hC0).mp
      have he : (d ^ gap' * (t ^ (1 - c) / C)) * C = d ^ gap' * t ^ (1 - c) := by field_simp
      rw [he]
      nlinarith only [hmul]
    exact hfirst.trans hmul'
  exact ⟨hraw, by linarith, hu0, by linarith, humesh, hlmesh, by linarith, hlutop⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
