-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeClockAtSample, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordPaletteResolution
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Glue
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeClockScales

/-!
# The native clock of one sample (session x1082)

At the child offset `c = childOffset κ₁ Ep precision gain m` of the stages, with
`X = (Ep+1) precision + 3` and `a = gain L`, the relative child clock `Tq = T_(i+c) - T_i` of a
path (grid `s l = (l+1)/m`, depths `|r_l - s_l L| ≤ δ₀ L`, clocks
`N^((κ₁ s_l - δ₀) L) ≤ 2^T_l ≤ N^((κ₁ s_l + δ₀) L)` at the two levels) satisfies:

* `native_clock_exponent_bounds`: `X a ≤ ch ≤ clockCoeff Ep precision * a` for the native
  exponent `ch = nativeClockExponent N Tq` (`2^Tq = N^ch`), and `T_i < T_(i+c)`;
* `native_theta_floor`: the final `θ = thetaOf …` is at least `N^-(3 X a/κ₁)`;
* `native_theta_ceiling`: `θ ≤ 2 N^(4 δ₀ L)` (the factor `2` of the dyadic thicknesses stays when
  `κ₁ = 1`), hence `θ ≤ N^(4 δ₀ L + margin)` whenever `2 ≤ N^margin`;
* `native_clock_power`: `(2^-Tq)^(M + 1/8) ≤ N^-(2 · 3 X a/κ₁)` for `M = qualDegree κ₁`, and
  `2 ≤ M`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification.Jets2

noncomputable section

section Clock

variable {N L κ₁ precision loss gain δ₀ : ℝ} {Ep m i : ℕ} {s r : ℕ → ℝ} {T : ℕ → ℕ}

/-- The depth of the child level over the root level is `c/m`. -/
theorem childOffset_depth_gap (hs : ∀ l, s l = ((l : ℝ) + 1) / m) :
    s (i + childOffset κ₁ Ep precision gain m) - s i =
      (childOffset κ₁ Ep precision gain m : ℝ) / m := by
  rw [hs, hs]; push_cast; ring

/-- **The native clock exponent of the child offset.** -/
theorem native_clock_exponent_bounds (hN : 1 < N) (hL : 0 < L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hprec : 1 ≤ precision) (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain / 100) (hm : 0 < m)
    (hgm : 8 ≤ gain * (m : ℝ)) (hs : ∀ l, s l = ((l : ℝ) + 1) / m)
    (hTAlo : N ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i)
    (hTAhi : (2 : ℝ) ^ T i ≤ N ^ ((κ₁ * s i + δ₀) * L))
    (hTBlo : N ^ ((κ₁ * s (i + childOffset κ₁ Ep precision gain m) - δ₀) * L) ≤
      (2 : ℝ) ^ T (i + childOffset κ₁ Ep precision gain m))
    (hTBhi : (2 : ℝ) ^ T (i + childOffset κ₁ Ep precision gain m) ≤
      N ^ ((κ₁ * s (i + childOffset κ₁ Ep precision gain m) + δ₀) * L)) :
    T i < T (i + childOffset κ₁ Ep precision gain m) ∧
      (((Ep : ℝ) + 1) * precision + 3) * (gain * L) ≤
        nativeClockExponent N (T (i + childOffset κ₁ Ep precision gain m) - T i) ∧
      nativeClockExponent N (T (i + childOffset κ₁ Ep precision gain m) - T i) ≤
        NativeDesign.clockCoeff Ep precision * (gain * L) := by
  set c := childOffset κ₁ Ep precision gain m with hc
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hgap := childOffset_depth_gap (κ₁ := κ₁) (Ep := Ep) (precision := precision) (gain := gain)
    (i := i) hs
  rw [← hc] at hgap
  have hlow := childOffset_lower (κ₁ := κ₁) (precision := precision) (gain := gain) (Ep := Ep) hκ hm
  rw [← hc] at hlow
  have hdepth := childOffset_depth_bound (L := L) (δ₀ := δ₀) (Ep := Ep) hκ hκ1 hprec hgain hδ
    hL.le hm hgm
  rw [← hc] at hdepth
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hX4 : (4 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by nlinarith
  -- `κ₁ c/m ≥ 2 (X - 1) gain`
  have hκc : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain ≤ κ₁ * ((c : ℝ) / m) := by
    have := mul_le_mul_of_nonneg_left hlow hκ.le
    rwa [mul_div_cancel₀ _ hκ.ne'] at this
  -- the strict order of the two clocks
  have hexp : (κ₁ * s i + δ₀) * L < (κ₁ * s (i + c) - δ₀) * L := by
    apply mul_lt_mul_of_pos_right _ hL
    have : s (i + c) = s i + (c : ℝ) / m := by linarith
    rw [this]
    nlinarith
  have hTlt : (2 : ℝ) ^ T i < (2 : ℝ) ^ T (i + c) :=
    hTAhi.trans_lt ((Real.rpow_lt_rpow_left_iff hN).mpr hexp |>.trans_le hTBlo)
  have hTlt' : T i < T (i + c) := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hTlt
  refine ⟨hTlt', ?_⟩
  -- the native exponent is the difference of the two clock exponents
  have h2A : (0 : ℝ) < (2 : ℝ) ^ T i := by positivity
  have h2B : (0 : ℝ) < (2 : ℝ) ^ T (i + c) := by positivity
  have hch : nativeClockExponent N (T (i + c) - T i) =
      Real.logb N ((2 : ℝ) ^ T (i + c)) - Real.logb N ((2 : ℝ) ^ T i) := by
    rw [nativeClockExponent, pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) hTlt'.le, ← div_eq_mul_inv,
      Real.logb_div h2B.ne' h2A.ne']
  have hlogAlo : (κ₁ * s i - δ₀) * L ≤ Real.logb N ((2 : ℝ) ^ T i) := by
    have := Real.logb_le_logb_of_le hN (by positivity) hTAlo
    rwa [Real.logb_rpow hN0 hN.ne'] at this
  have hlogAhi : Real.logb N ((2 : ℝ) ^ T i) ≤ (κ₁ * s i + δ₀) * L := by
    have := Real.logb_le_logb_of_le hN h2A hTAhi
    rwa [Real.logb_rpow hN0 hN.ne'] at this
  have hlogBlo : (κ₁ * s (i + c) - δ₀) * L ≤ Real.logb N ((2 : ℝ) ^ T (i + c)) := by
    have := Real.logb_le_logb_of_le hN (by positivity) hTBlo
    rwa [Real.logb_rpow hN0 hN.ne'] at this
  have hlogBhi : Real.logb N ((2 : ℝ) ^ T (i + c)) ≤ (κ₁ * s (i + c) + δ₀) * L := by
    have := Real.logb_le_logb_of_le hN h2B hTBhi
    rwa [Real.logb_rpow hN0 hN.ne'] at this
  have hsb : s (i + c) = s i + (c : ℝ) / m := by linarith
  rw [hch]
  constructor
  · -- `ch ≥ κ₁ (c/m) L - 2 δ₀ L ≥ 2 (X-1) a - a/50 ≥ X a`
    have h1 : κ₁ * ((c : ℝ) / m) * L - 2 * δ₀ * L ≤
        Real.logb N ((2 : ℝ) ^ T (i + c)) - Real.logb N ((2 : ℝ) ^ T i) := by
      rw [hsb] at hlogBlo; nlinarith
    have h2 : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * L ≤ κ₁ * ((c : ℝ) / m) * L :=
      mul_le_mul_of_nonneg_right hκc hL.le
    have h3 : 2 * δ₀ * L ≤ gain * L / 50 := by nlinarith
    nlinarith
  · -- `ch ≤ κ₁ (c/m) L + 2 δ₀ L ≤ 2 X a + a/50 ≤ 4 X a`
    have h1 : Real.logb N ((2 : ℝ) ^ T (i + c)) - Real.logb N ((2 : ℝ) ^ T i) ≤
        κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L := by
      rw [hsb] at hlogBhi; nlinarith
    set P := gain * L with hP
    have hP0 : 0 < P := mul_pos hgain hL
    set X := ((Ep : ℝ) + 1) * precision + 3 with hXdef
    have hdepth' : ((c : ℝ) / m) * L ≤ 2 * X * P / κ₁ := by
      have h := hdepth
      rw [add_mul] at h
      have h' : 2 * X * gain * L / κ₁ = 2 * X * P / κ₁ := by rw [hP]; ring
      have hδL : 0 ≤ 2 * δ₀ * L := by positivity
      linarith
    have hκP : κ₁ * (2 * X * P / κ₁) = 2 * X * P := by field_simp
    have h2 : κ₁ * ((c : ℝ) / m) * L ≤ 2 * X * P := by
      have := mul_le_mul_of_nonneg_left hdepth' hκ.le
      rw [hκP] at this
      linarith [mul_assoc κ₁ ((c : ℝ) / m) L]
    have h3 : 2 * δ₀ * L ≤ P / 50 := by
      have : 2 * δ₀ * L ≤ 2 * (gain / 100) * L := by
        apply mul_le_mul_of_nonneg_right _ hL.le; linarith
      rw [hP]; linarith
    have hXP : 4 * P ≤ X * P := mul_le_mul_of_nonneg_right hX4 hP0.le
    have h4 : 2 * X * P + P / 50 ≤ 4 * X * P := by linarith only [hXP, hP0]
    show _ ≤ 4 * X * P
    linarith only [h1, h2, h3, h4]

/-- **The native floor of the final `θ`.** -/
theorem native_theta_floor (hN : 1 < N) (hL : 0 < L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hδ : δ₀ ≤ gain / 100) (hm : 0 < m) (hgm : 8 ≤ gain * (m : ℝ)) (h2 : 2 ≤ N ^ (gain * L))
    (hs : ∀ l, s l = ((l : ℝ) + 1) / m)
    (hrA : |r i - s i * L| ≤ δ₀ * L)
    (hrB : |r (i + childOffset κ₁ Ep precision gain m) -
      s (i + childOffset κ₁ Ep precision gain m) * L| ≤ δ₀ * L) :
    N ^ (-(3 * (((Ep : ℝ) + 1) * precision + 3) * (gain * L) / κ₁)) ≤
      thetaOf Ep precision loss gain N L (r i) (r (i + childOffset κ₁ Ep precision gain m)) (T i)
        (T (i + childOffset κ₁ Ep precision gain m)) := by
  set c := childOffset κ₁ Ep precision gain m with hc
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hgap := childOffset_depth_gap (κ₁ := κ₁) (Ep := Ep) (precision := precision) (gain := gain)
    (i := i) hs
  rw [← hc] at hgap
  have hdepth := childOffset_depth_bound (L := L) (δ₀ := δ₀) (Ep := Ep) hκ hκ1 hprec hgain hδ
    hL.le hm hgm
  rw [← hc] at hdepth
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have ha : 0 < gain * L := mul_pos hgain hL
  set X := ((Ep : ℝ) + 1) * precision + 3 with hX
  -- the depth increment
  have hrBA : r (i + c) - r i ≤ 2 * X * gain * L / κ₁ := by
    have h1 := (abs_le.mp hrA).1
    have h2 := (abs_le.mp hrB).2
    have : r (i + c) - r i ≤ ((c : ℝ) / m + 2 * δ₀) * L := by
      have hsb : s (i + c) = s i + (c : ℝ) / m := by linarith
      rw [hsb] at h2; nlinarith
    linarith
  -- the exponent of the palette mesh
  have hEp : (Ep : ℝ) * (precision * gain * L) ≤ (X - 4) * (gain * L) := by
    have : (Ep : ℝ) * precision ≤ X - 4 := by rw [hX]; nlinarith
    nlinarith
  have hK : (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤ 2 * (gain * L) := by
    have hE1 : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
    rw [show (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) = 2 * loss * (gain * L) by
      field_simp]
    nlinarith
  set e := (r (i + c) - r i) + (Ep : ℝ) * (precision * gain * L) +
    (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) with he
  have he_le : e + gain * L ≤ 3 * X * (gain * L) / κ₁ := by
    have hX4 : (4 : ℝ) ≤ X := by rw [hX]; nlinarith
    have h1 : (X - 1) * (gain * L) ≤ (X - 1) * (gain * L) / κ₁ := by
      rw [le_div_iff₀ hκ]
      exact mul_le_of_le_one_right (by nlinarith) hκ1
    have h2 : 2 * X * gain * L / κ₁ = 2 * X * (gain * L) / κ₁ := by ring
    have h3 : 2 * X * (gain * L) / κ₁ + (X - 1) * (gain * L) / κ₁ = (3 * X - 1) * (gain * L) / κ₁ := by
      ring
    have h4 : (3 * X - 1) * (gain * L) / κ₁ ≤ 3 * X * (gain * L) / κ₁ := by
      apply div_le_div_of_nonneg_right _ hκ.le; nlinarith
    linarith
  -- `θ ≥ pv ≥ N^-e/2 ≥ N^-(e + a)`
  have hpv := pvOf_lower_power (N := N) (L := L) (rA := r i) (rB := r (i + c))
    (precision := precision) (loss := loss) (gain := gain) Ep (T i) (T (i + c)) hN0
  have hKge : 1 ≤ KOf Ep loss gain N L ^ (Ep + 2) := by
    apply one_le_pow₀
    unfold KOf
    exact Real.one_le_rpow hN.le (by positivity)
  have hθpv : pvOf Ep precision loss gain N L (r i) (r (i + c)) (T i) (T (i + c)) ≤
      thetaOf Ep precision loss gain N L (r i) (r (i + c)) (T i) (T (i + c)) := by
    unfold pvOf
    have hθ0 : 0 ≤ thetaOf Ep precision loss gain N L (r i) (r (i + c)) (T i) (T (i + c)) := by
      have := (by positivity : (0 : ℝ) ≤ N ^ (-e) / 2).trans hpv
      unfold pvOf at this
      have hKpos : 0 < KOf Ep loss gain N L ^ (Ep + 2) := lt_of_lt_of_le one_pos hKge
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hKpos))
    exact div_le_self hθ0 hKge
  have hhalf : N ^ (-(e + gain * L)) ≤ N ^ (-e) / 2 := by
    have hNa : N ^ (-(gain * L)) ≤ 2⁻¹ := by
      rw [Real.rpow_neg hN0.le]
      exact inv_anti₀ (by norm_num) h2
    rw [neg_add, Real.rpow_add hN0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hNa (by positivity)
  calc N ^ (-(3 * X * (gain * L) / κ₁)) ≤ N ^ (-(e + gain * L)) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    _ ≤ N ^ (-e) / 2 := hhalf
    _ ≤ _ := hpv.trans hθpv

/-- **The ceiling of the final `θ`.** -/
theorem native_theta_ceiling (hN : 1 < N) (hL : 0 < L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hprec : 1 ≤ precision) (hloss : 0 ≤ loss) (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀)
    (hδ : δ₀ ≤ gain / 100) (hm : 0 < m) (hgm : 8 ≤ gain * (m : ℝ)) (h2 : 2 ≤ N ^ (gain * L))
    (hs : ∀ l, s l = ((l : ℝ) + 1) / m)
    (hrA : |r i - s i * L| ≤ δ₀ * L)
    (hrB : |r (i + childOffset κ₁ Ep precision gain m) -
      s (i + childOffset κ₁ Ep precision gain m) * L| ≤ δ₀ * L)
    (hTAlo : N ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i)
    (hTAhi : (2 : ℝ) ^ T i ≤ N ^ ((κ₁ * s i + δ₀) * L))
    (hTBlo : N ^ ((κ₁ * s (i + childOffset κ₁ Ep precision gain m) - δ₀) * L) ≤
      (2 : ℝ) ^ T (i + childOffset κ₁ Ep precision gain m))
    (hTBhi : (2 : ℝ) ^ T (i + childOffset κ₁ Ep precision gain m) ≤
      N ^ ((κ₁ * s (i + childOffset κ₁ Ep precision gain m) + δ₀) * L)) :
    thetaOf Ep precision loss gain N L (r i) (r (i + childOffset κ₁ Ep precision gain m)) (T i)
      (T (i + childOffset κ₁ Ep precision gain m)) ≤ 2 * N ^ (4 * δ₀ * L) := by
  set c := childOffset κ₁ Ep precision gain m with hc
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hgap := childOffset_depth_gap (κ₁ := κ₁) (Ep := Ep) (precision := precision) (gain := gain)
    (i := i) hs
  rw [← hc] at hgap
  have hTlt := (native_clock_exponent_bounds (Ep := Ep) hN hL hκ hκ1 hprec hgain hδ0
    hδ hm hgm hs hTAlo hTAhi hTBlo hTBhi).1
  rw [← hc] at hTlt
  have hsb : s (i + c) = s i + (c : ℝ) / m := by linarith
  have hcm0 : (0 : ℝ) ≤ (c : ℝ) / m := by positivity
  -- `ζ^Ep / K^Ep ≤ 1`
  have hζ0 : 0 ≤ zetaOf precision gain N L := (O204.Tangent.δ_pos N _).le
  have hζ1 : zetaOf precision gain N L ≤ 1 := by
    have h := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0
      (precision * gain * L)).2
    have hpow : N ^ (gain * L) ≤ N ^ (precision * gain * L) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by nlinarith [mul_pos hgain hL])
    have : 2 * N ^ (-(precision * gain * L)) ≤ 1 := by
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one (by positivity)]
      linarith
    exact h.trans this
  have hK1 : 1 ≤ KOf Ep loss gain N L := by
    unfold KOf; exact Real.one_le_rpow hN.le (by positivity)
  have hzK : zetaOf precision gain N L ^ Ep / KOf Ep loss gain N L ^ Ep ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (pow_le_one₀ hζ0 hζ1).trans (one_le_pow₀ hK1)
  have hzK0 : 0 ≤ zetaOf precision gain N L ^ Ep / KOf Ep loss gain N L ^ Ep := by positivity
  -- `a'/h' ≤ 2 N^(4 δ₀ L)`
  have haRel : aRelOf N (r i) (r (i + c)) ≤ 2 * N ^ (r i - r (i + c)) := by
    unfold aRelOf
    have hB := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0 (r (i + c))).2
    have hA := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0 (r i)).1
    have hA0 : 0 < N ^ (-r i) := Real.rpow_pos_of_pos hN0 _
    rw [div_le_iff₀ (O204.Tangent.δ_pos N _)]
    calc O204.Split.δ N (r (i + c)) ≤ 2 * N ^ (-r (i + c)) := hB
      _ = 2 * N ^ (r i - r (i + c)) * N ^ (-r i) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
      _ ≤ 2 * N ^ (r i - r (i + c)) * O204.Split.δ N (r i) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
  have hhRel : (hRelOf (T i) (T (i + c)))⁻¹ ≤ N ^ (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L) := by
    unfold hRelOf
    rw [inv_inv, pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) hTlt.le, ← div_eq_mul_inv,
      div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ T (i + c) ≤ N ^ ((κ₁ * s (i + c) + δ₀) * L) := hTBhi
      _ = N ^ (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L) * N ^ ((κ₁ * s i - δ₀) * L) := by
          rw [← Real.rpow_add hN0, hsb]; ring_nf
      _ ≤ N ^ (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L) * (2 : ℝ) ^ T i :=
          mul_le_mul_of_nonneg_left hTAlo (by positivity)
  have hrBA : (c : ℝ) / m * L - 2 * δ₀ * L ≤ r (i + c) - r i := by
    have h1 := (abs_le.mp hrA).2
    have h2 := (abs_le.mp hrB).1
    rw [hsb] at h2; nlinarith
  have hexp : (r i - r (i + c)) + (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L) ≤ 4 * δ₀ * L := by
    have : κ₁ * ((c : ℝ) / m) * L ≤ (c : ℝ) / m * L := by
      have := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hcm0 hL.le)
      linarith
    linarith
  have haRel0 : 0 ≤ aRelOf N (r i) (r (i + c)) := by
    unfold aRelOf; exact div_nonneg (O204.Tangent.δ_pos N _).le (O204.Tangent.δ_pos N _).le
  unfold thetaOf
  calc aRelOf N (r i) (r (i + c)) / hRelOf (T i) (T (i + c)) * zetaOf precision gain N L ^ Ep /
        KOf Ep loss gain N L ^ Ep
      = aRelOf N (r i) (r (i + c)) * (hRelOf (T i) (T (i + c)))⁻¹ *
          (zetaOf precision gain N L ^ Ep / KOf Ep loss gain N L ^ Ep) := by ring
    _ ≤ (2 * N ^ (r i - r (i + c))) * N ^ (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L) * 1 := by
        have hinv0 : 0 ≤ (hRelOf (T i) (T (i + c)))⁻¹ := by
          unfold hRelOf; rw [inv_inv]; positivity
        exact mul_le_mul (mul_le_mul haRel hhRel hinv0 (by positivity)) hzK hzK0 (by positivity)
    _ = 2 * N ^ ((r i - r (i + c)) + (κ₁ * ((c : ℝ) / m) * L + 2 * δ₀ * L)) := by
        rw [mul_one, mul_assoc, ← Real.rpow_add hN0]
    _ ≤ 2 * N ^ (4 * δ₀ * L) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN.le hexp) (by norm_num)

/-- The ceiling of `θ` at any margin paying the factor `2`. -/
theorem native_theta_ceiling_margin {margin : ℝ} (hN : 1 < N) (hmargin : 2 ≤ N ^ margin)
    {θ : ℝ} (hθ : θ ≤ 2 * N ^ (4 * δ₀ * L)) : θ ≤ N ^ (4 * δ₀ * L + margin) := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  rw [Real.rpow_add hN0]
  calc θ ≤ 2 * N ^ (4 * δ₀ * L) := hθ
    _ ≤ N ^ margin * N ^ (4 * δ₀ * L) := mul_le_mul_of_nonneg_right hmargin (by positivity)
    _ = _ := mul_comm _ _

/-- **The power of the native clock length.** -/
theorem native_clock_power (hN : 1 < N) (hκ : 0 < κ₁) {X a : ℝ} (hX : 0 ≤ X)
    (ha : 0 ≤ a) {Tq : ℕ} (hch : X * a ≤ nativeClockExponent N Tq) :
    ((2 : ℝ) ^ Tq)⁻¹ ^ ((qualDegree κ₁ : ℝ) + 1 / 8) ≤ N ^ (-(2 * (3 * X * a / κ₁))) ∧
      2 ≤ qualDegree κ₁ := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hM8 : 8 / κ₁ ≤ (qualDegree κ₁ : ℝ) := by
    unfold qualDegree; push_cast
    have := Nat.le_ceil (8 / κ₁)
    linarith
  have hM2 : 2 ≤ qualDegree κ₁ := by
    unfold qualDegree
    have : 1 ≤ ⌈8 / κ₁⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
    omega
  refine ⟨?_, hM2⟩
  rw [← nativeClockExponent_width hN, ← Real.rpow_mul hN0.le]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  have hch0 : 0 ≤ nativeClockExponent N Tq := (mul_nonneg hX ha).trans hch
  have hXa : 0 ≤ X * a := mul_nonneg hX ha
  have h1 : 8 * (X * a) / κ₁ ≤ nativeClockExponent N Tq * (qualDegree κ₁ : ℝ) := by
    calc 8 * (X * a) / κ₁ = X * a * (8 / κ₁) := by ring
      _ ≤ nativeClockExponent N Tq * (qualDegree κ₁ : ℝ) :=
          mul_le_mul hch hM8 (by positivity) hch0
  have h2 : 2 * (3 * X * a / κ₁) ≤ 8 * (X * a) / κ₁ := by
    rw [show 2 * (3 * X * a / κ₁) = 6 * (X * a) / κ₁ by ring]
    exact div_le_div_of_nonneg_right (by linarith) hκ.le
  nlinarith

end Clock

section Path

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}

/-- **The native clock of one sample**, read on the path: all of the above at the levels `i` and
`i + childOffset`. -/
theorem native_clock_at_path (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    {precision loss gain : ℝ} {Ep i : ℕ}
    (hN : 1 < Nk) (hL : 0 < L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprec : 1 ≤ precision)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀)
    (hδ : δ₀ ≤ gain / 100) (hgm : 8 ≤ gain * (m : ℝ)) (h2 : 2 ≤ Nk ^ (gain * L))
    (hs : ∀ l, s l = ((l : ℝ) + 1) / m) (hib : i + childOffset κ₁ Ep precision gain m < m) :
    p.T i < p.T (i + childOffset κ₁ Ep precision gain m) ∧
      (((Ep : ℝ) + 1) * precision + 3) * (gain * L) ≤
        nativeClockExponent Nk (p.T (i + childOffset κ₁ Ep precision gain m) - p.T i) ∧
      nativeClockExponent Nk (p.T (i + childOffset κ₁ Ep precision gain m) - p.T i) ≤
        NativeDesign.clockCoeff Ep precision * (gain * L) ∧
      Nk ^ (-(3 * (((Ep : ℝ) + 1) * precision + 3) * (gain * L) / κ₁)) ≤
        thetaOf Ep precision loss gain Nk L (p.r i) (p.r (i + childOffset κ₁ Ep precision gain m))
          (p.T i) (p.T (i + childOffset κ₁ Ep precision gain m)) ∧
      thetaOf Ep precision loss gain Nk L (p.r i) (p.r (i + childOffset κ₁ Ep precision gain m))
          (p.T i) (p.T (i + childOffset κ₁ Ep precision gain m)) ≤ 2 * Nk ^ (4 * δ₀ * L) ∧
      ((2 : ℝ) ^ (p.T (i + childOffset κ₁ Ep precision gain m) - p.T i))⁻¹ ^
          ((qualDegree κ₁ : ℝ) + 1 / 8) ≤
        Nk ^ (-(2 * (3 * (((Ep : ℝ) + 1) * precision + 3) * (gain * L) / κ₁))) ∧
      2 ≤ qualDegree κ₁ := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hib
  have hi : i < m := lt_of_le_of_lt (Nat.le_add_right _ _) hib
  have hA := hp.2.2.2.2.1 i hi
  have hB := hp.2.2.2.2.1 _ hib
  obtain ⟨hTlt, hlo, hhi⟩ := native_clock_exponent_bounds (Ep := Ep) hN hL hκ hκ1 hprec hgain hδ0
    hδ hm hgm hs hA.2.2.1 hA.2.2.2.1 hB.2.2.1 hB.2.2.2.1
  have hX : (0 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by positivity
  obtain ⟨hpow, hM⟩ := native_clock_power hN hκ hX (mul_pos hgain hL).le hlo
  exact ⟨hTlt, hlo, hhi,
    native_theta_floor (T := p.T) hN hL hκ hκ1 hprec hloss hloss1 hgain hδ hm hgm h2 hs hA.1 hB.1,
    native_theta_ceiling hN hL hκ hκ1 hprec hloss.le hgain hδ0 hδ hm hgm h2 hs hA.1 hB.1
      hA.2.2.1 hA.2.2.2.1 hB.2.2.1 hB.2.2.2.1, hpow, hM⟩

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
