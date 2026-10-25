-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AnisotropicLineCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicStripDiameter
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Line nonconcentration survives anisotropic expansion. Nearly longitudinal
normals are controlled by the original ball Frostman bound. -/
theorem anisotropic_line_count {I : Type*} [Fintype I] {f : I → Plane}
    {δ C K ζ h q c : ℝ} {e : Plane}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hK : 1 ≤ K) (hζ : 0 ≤ ζ)
    (hδh : δ ≤ h) (hh1 : h ≤ 1) (hδq : δ ≤ q) (hq : q ≤ 1 / 2)
    (he : ‖e‖ = 1) (hF : IndexedFrostman δ C f)
    (hstrip : ∀ i, |inner ℝ (f i) (perp e) - c| ≤ h)
    (hsmall : 10 * C * q ≤ δ ^ ζ)
    (hline : ∀ (u : Plane) (d s : ℝ), ‖u‖ = 1 → δ ≤ s →
      ((Finset.univ.filter (fun i => |inner ℝ (f i) u - d| < s)).card : ℝ) ≤
        K * (s / h) ^ ζ * (Fintype.card I : ℝ)) :
    ∀ (n : Plane) (d r : ℝ), ‖n‖ = 1 → δ / h ≤ r →
      ((Finset.univ.filter (fun i => |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r)).card : ℝ) ≤
        K * (r / q) ^ ζ * (Fintype.card I : ℝ) := by
  classical
  have hh : 0 < h := hδ.trans_le hδh
  have hqpos : 0 < q := hδ.trans_le hδq
  intro n d r hn hδr
  have hr : 0 < r := (div_pos hδ hh).trans_le hδr
  have hδr' : δ ≤ r := by
    have hh' : δ ≤ δ / h := (le_div_iff₀ hh).mpr (by nlinarith)
    exact hh'.trans hδr
  by_cases hqr : q ≤ r
  · have hcard : ((Finset.univ.filter (fun i =>
        |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r)).card : ℝ) ≤ (Fintype.card I : ℝ) := by
      exact_mod_cast (Finset.card_filter_le Finset.univ _).trans_eq Finset.card_univ
    have hpow : 1 ≤ (r / q) ^ ζ := Real.one_le_rpow ((one_le_div hqpos).mpr hqr) hζ
    have hcoef : 1 ≤ K * (r / q) ^ ζ := by
      simpa only [one_mul] using mul_le_mul hK hpow zero_le_one (zero_le_one.trans hK)
    exact hcard.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (Fintype.card I)))
  have hrq : r ≤ q := (lt_of_not_ge hqr).le
  by_cases hnormal : q ≤ h ∨ q ≤ |inner ℝ n (perp e)|
  · let v := anisotropicMap e 1 h⁻¹ n
    obtain ⟨hv1, hvh, hnv⟩ := anisotropic_normal_bounds he hn hh hh1
    have hv : 0 < ‖v‖ := zero_lt_one.trans_le hv1
    obtain ⟨u, hu, hpull⟩ := anisotropic_strip_pullback he hn hh hh1 d r
    have hδs : δ ≤ r / ‖v‖ := by
      apply (le_div_iff₀ hv).mpr
      calc δ * ‖v‖ ≤ δ * h⁻¹ := mul_le_mul_of_nonneg_left hvh hδ.le
        _ = δ / h := by ring
        _ ≤ r := hδr
    have hden : q ≤ h * ‖v‖ := by
      rcases hnormal with hqh | hqn
      · exact hqh.trans (by nlinarith)
      · exact hqn.trans hnv
    have hfilt : Finset.univ.filter (fun i => |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r) =
        Finset.univ.filter (fun i => |inner ℝ (f i) u - d / ‖v‖| < r / ‖v‖) := by
      apply Finset.filter_congr
      intro i hi
      exact hpull (f i)
    rw [hfilt]
    have hbound := hline u (d / ‖v‖) (r / ‖v‖) hu hδs
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
    apply Real.rpow_le_rpow (by positivity) _ hζ
    calc r / ‖v‖ / h = r / (h * ‖v‖) := by ring
      _ ≤ r / q := div_le_div_of_nonneg_left hr.le hqpos hden
  have hhq : h ≤ q := (lt_of_not_ge (fun h => hnormal (Or.inl h))).le
  have hnq : |inner ℝ n (perp e)| ≤ q := (lt_of_not_ge (fun h => hnormal (Or.inr h))).le
  have hcount := hF.card_of_diameter
    (Finset.univ.filter (fun i => |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r))
    hC (by positivity : 0 ≤ 10 * q) (by linarith : δ ≤ 10 * q) (by
      intro i hi j hj
      exact anisotropic_parallel_strip_diameter he hn hh hhq hq hrq hnq
        (hstrip i) (hstrip j) (Finset.mem_filter.mp hi).2.le (Finset.mem_filter.mp hj).2.le)
  calc ((Finset.univ.filter (fun i => |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r)).card : ℝ) ≤
        C * (10 * q) * (Fintype.card I : ℝ) := hcount
    _ ≤ δ ^ ζ * (Fintype.card I : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      nlinarith
    _ ≤ r ^ ζ * (Fintype.card I : ℝ) := by
      gcongr
    _ ≤ (r / q) ^ ζ * (Fintype.card I : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow hr.le _ hζ
      exact (le_div_iff₀ hqpos).mpr (by nlinarith)
    _ ≤ K * (r / q) ^ ζ * (Fintype.card I : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (by positivity) ζ)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
