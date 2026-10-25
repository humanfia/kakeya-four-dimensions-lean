-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.ConvexEnlarge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Zoom

/-!
# Enlarging a convex set by its difference body

For a bounded convex set `W ⊆ ℝ³` and `t ≥ 0`,

  `|W + t (W - W)| ≤ (1 + 4t)³ |W|`.

If `W` has empty interior, both sides vanish (`W` lies in a proper affine subspace). Otherwise
take four points of `K = closure W` maximizing the determinant `|det(a₁ - a₀, a₂ - a₀, a₃ - a₀)|`.
Replacing a vertex by a point `q ∈ K` multiplies the determinant by the corresponding
barycentric coordinate of `q`, so all barycentric coordinates are at most `1`, and with
`g = (a₀ + a₁ + a₂ + a₃) / 4` the point `g + (g - q) / 3` is a convex combination of the
vertices: `g - q ∈ 3 (K - g)`. Hence `W + t (W - W) ⊆ g + (1 + 4t) (K - g)`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space)

/-- The determinant of three vectors. -/
def det3 (u v w : Space) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- The signed volume (times six) of a tetrahedron. -/
def tdet (a0 a1 a2 a3 : Space) : ℝ := det3 (a1 - a0) (a2 - a0) (a3 - a0)

theorem continuous_tdet :
    Continuous (fun a : Space × Space × Space × Space => tdet a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  unfold tdet det3
  fun_prop

/-- The four sub-tetrahedra obtained by replacing one vertex by `q` add up. -/
theorem tdet_sum (a0 a1 a2 a3 q : Space) :
    tdet q a1 a2 a3 + tdet a0 q a2 a3 + tdet a0 a1 q a3 + tdet a0 a1 a2 q = tdet a0 a1 a2 a3 := by
  simp only [tdet, det3, PiLp.sub_apply]
  ring

/-- Cramer's rule for barycentric coordinates. -/
theorem tdet_cramer0 (a0 a1 a2 a3 q : Space) :
    tdet a0 a1 a2 a3 * q 0 = tdet q a1 a2 a3 * a0 0 + tdet a0 q a2 a3 * a1 0 +
      tdet a0 a1 q a3 * a2 0 + tdet a0 a1 a2 q * a3 0 := by
  simp only [tdet, det3, PiLp.sub_apply]; ring

theorem tdet_cramer1 (a0 a1 a2 a3 q : Space) :
    tdet a0 a1 a2 a3 * q 1 = tdet q a1 a2 a3 * a0 1 + tdet a0 q a2 a3 * a1 1 +
      tdet a0 a1 q a3 * a2 1 + tdet a0 a1 a2 q * a3 1 := by
  simp only [tdet, det3, PiLp.sub_apply]; ring

theorem tdet_cramer2 (a0 a1 a2 a3 q : Space) :
    tdet a0 a1 a2 a3 * q 2 = tdet q a1 a2 a3 * a0 2 + tdet a0 q a2 a3 * a1 2 +
      tdet a0 a1 q a3 * a2 2 + tdet a0 a1 a2 q * a3 2 := by
  simp only [tdet, det3, PiLp.sub_apply]; ring

/-- Three points with positive determinant near any interior point. -/
theorem exists_tdet_pos {W : Set Space} (hW : (interior W).Nonempty) :
    ∃ b0 ∈ W, ∃ b1 ∈ W, ∃ b2 ∈ W, ∃ b3 ∈ W, 0 < |tdet b0 b1 b2 b3| := by
  obtain ⟨p, hp⟩ := hW
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  set s' := s / 2 with hs'
  have hs'0 : 0 < s' := by positivity
  have hmem : ∀ i : Fin 3, p + s' • EuclideanSpace.single i (1 : ℝ) ∈ W := by
    intro i
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single,
      norm_one, mul_one, Real.norm_eq_abs, abs_of_pos hs'0]
    linarith
  refine ⟨p, interior_subset (hball (mem_ball_self hs)), _, hmem 0, _, hmem 1, _, hmem 2, ?_⟩
  have : tdet p (p + s' • EuclideanSpace.single 0 (1 : ℝ)) (p + s' • EuclideanSpace.single 1 1)
      (p + s' • EuclideanSpace.single 2 1) = s' ^ 3 := by
    simp only [tdet, det3, add_sub_cancel_left, PiLp.smul_apply, smul_eq_mul,
      EuclideanSpace.single_apply]
    simp
    ring
  rw [this, abs_of_pos (by positivity)]
  positivity

/-- Convex combinations of four points. -/
theorem convex_comb4 {K : Set Space} (hK : Convex ℝ K) {a b c d : Space} (ha : a ∈ K)
    (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) {w0 w1 w2 w3 : ℝ} (h0 : 0 ≤ w0) (h1 : 0 ≤ w1)
    (h2 : 0 ≤ w2) (h3 : 0 ≤ w3) (hs : w0 + w1 + w2 + w3 = 1) :
    w0 • a + w1 • b + w2 • c + w3 • d ∈ K := by
  have hab : (w0 + w1) • ((w0 / (w0 + w1)) • a + (w1 / (w0 + w1)) • b) = w0 • a + w1 • b ∨
      w0 + w1 = 0 := by
    by_cases h : w0 + w1 = 0
    · exact Or.inr h
    · left
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h, mul_div_cancel₀ _ h]
  have key : ∀ {x y : Space} {p q : ℝ}, x ∈ K → y ∈ K → 0 ≤ p → 0 ≤ q → p + q = 1 →
      p • x + q • y ∈ K := fun hx hy hp hq hpq => hK hx hy hp hq hpq
  -- combine step by step
  by_cases h01 : w0 + w1 = 0
  · have hw0 : w0 = 0 := by linarith
    have hw1 : w1 = 0 := by linarith
    subst hw0 hw1
    simp only [zero_smul, zero_add]
    by_cases h23 : w2 + w3 = 0
    · exfalso; linarith
    · simp only [zero_add] at hs
      exact key hc hd h2 h3 hs
  by_cases h012 : w0 + w1 + w2 = 0
  · exfalso
    have : w2 = 0 := by linarith
    have : w0 + w1 = 0 := by linarith
    exact h01 this
  have hp01 : 0 < w0 + w1 := lt_of_le_of_ne (by linarith) (Ne.symm h01)
  have hp012 : 0 < w0 + w1 + w2 := lt_of_le_of_ne (by linarith) (Ne.symm h012)
  set x1 := (w0 / (w0 + w1)) • a + (w1 / (w0 + w1)) • b with hx1
  have hx1K : x1 ∈ K := key ha hb (by positivity) (by positivity) (by field_simp)
  set x2 := ((w0 + w1) / (w0 + w1 + w2)) • x1 + (w2 / (w0 + w1 + w2)) • c with hx2
  have hx2K : x2 ∈ K := key hx1K hc (by positivity) (by positivity) (by field_simp)
  have hfin := key hx2K hd (by linarith : 0 ≤ w0 + w1 + w2) h3 (by linarith)
  have he : (w0 + w1 + w2) • x2 + w3 • d = w0 • a + w1 • b + w2 • c + w3 • d := by
    rw [hx2, hx1]
    apply space_ext3 <;>
      (simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
       field_simp
       try ring)
  rwa [he] at hfin

/-- **The difference-body enlargement of a bounded convex set.** -/
theorem volume_add_smul_sub_le {W : Set Space} (hW : Convex ℝ W) (hWb : Bornology.IsBounded W)
    {t : ℝ} (ht : 0 ≤ t) :
    volume (W + t • (W - W)) ≤ ENNReal.ofReal ((1 + 4 * t) ^ 3) * volume W := by
  classical
  by_cases hint : (interior W).Nonempty
  swap
  · -- degenerate case: everything lies in a proper affine subspace
    have hspan : affineSpan ℝ W ≠ ⊤ := by
      intro h
      exact hint ((hW.interior_nonempty_iff_affineSpan_eq_top).mpr h)
    have hsub : W + t • (W - W) ⊆ (affineSpan ℝ W : Set Space) := by
      rintro _ ⟨w, hw, _, ⟨d, ⟨w1, hw1, w2, hw2, rfl⟩, rfl⟩, rfl⟩
      have hdir : t • (w1 - w2) ∈ (affineSpan ℝ W).direction := by
        rw [direction_affineSpan]
        exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hw1 hw2)
      have := AffineSubspace.vadd_mem_of_mem_direction hdir (subset_affineSpan ℝ W hw)
      rwa [vadd_eq_add, add_comm] at this
    have h0 : volume (W + t • (W - W)) = 0 :=
      measure_mono_null hsub (Measure.addHaar_affineSubspace volume _ hspan)
    rw [h0]
    exact zero_le
  -- the compact closure and a tetrahedron of maximal determinant
  set K := closure W with hKdef
  have hKc : IsCompact K := hWb.isCompact_closure
  have hKconv : Convex ℝ K := hW.closure
  have hWK : W ⊆ K := subset_closure
  have hK4 : IsCompact (K ×ˢ K ×ˢ K ×ˢ K) := hKc.prod (hKc.prod (hKc.prod hKc))
  obtain ⟨b0, hb0, b1, hb1, b2, hb2, b3, hb3, hbpos⟩ := exists_tdet_pos hint
  obtain ⟨a, ha, hmax⟩ := hK4.exists_isMaxOn
    ⟨(b0, b1, b2, b3), hWK hb0, hWK hb1, hWK hb2, hWK hb3⟩
    (continuous_abs.comp continuous_tdet).continuousOn
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  set a0 := a.1
  set a1 := a.2.1
  set a2 := a.2.2.1
  set a3 := a.2.2.2
  set D := tdet a0 a1 a2 a3 with hD
  have hmax' : ∀ c0 ∈ K, ∀ c1 ∈ K, ∀ c2 ∈ K, ∀ c3 ∈ K, |tdet c0 c1 c2 c3| ≤ |D| := by
    intro c0 h0 c1 h1 c2 h2 c3 h3
    exact hmax (show (c0, c1, c2, c3) ∈ K ×ˢ K ×ˢ K ×ˢ K from ⟨h0, h1, h2, h3⟩)
  have hDpos : 0 < |D| :=
    hbpos.trans_le (hmax' b0 (hWK hb0) b1 (hWK hb1) b2 (hWK hb2) b3 (hWK hb3))
  have hD0 : D ≠ 0 := abs_pos.mp hDpos
  set g : Space := (1 / 4 : ℝ) • (a0 + a1 + a2 + a3) with hg
  -- the point reflected through `g` and shrunk by `3` stays in `K`
  have hrefl : ∀ q ∈ K, ∃ q' ∈ K, g - q = (3 : ℝ) • (q' - g) := by
    intro q hq
    set D0 := tdet q a1 a2 a3
    set D1 := tdet a0 q a2 a3
    set D2 := tdet a0 a1 q a3
    set D3 := tdet a0 a1 a2 q
    have hsum : D0 + D1 + D2 + D3 = D := tdet_sum a0 a1 a2 a3 q
    have hle : ∀ Di : ℝ, |Di| ≤ |D| → 0 ≤ (D - Di) / (3 * D) := by
      intro Di hDi
      have h1 : Di / D ≤ 1 := by
        have := (abs_div Di D) ▸ (div_le_one hDpos).mpr hDi
        exact (le_abs_self _).trans this
      have h2 : (D - Di) / (3 * D) = (1 - Di / D) / 3 := by field_simp
      rw [h2]
      linarith
    have hw0 := hle D0 (hmax' q hq a1 ha1 a2 ha2 a3 ha3)
    have hw1 := hle D1 (hmax' a0 ha0 q hq a2 ha2 a3 ha3)
    have hw2 := hle D2 (hmax' a0 ha0 a1 ha1 q hq a3 ha3)
    have hw3 := hle D3 (hmax' a0 ha0 a1 ha1 a2 ha2 q hq)
    have hws : (D - D0) / (3 * D) + (D - D1) / (3 * D) + (D - D2) / (3 * D) +
        (D - D3) / (3 * D) = 1 := by
      field_simp
      linarith
    refine ⟨((D - D0) / (3 * D)) • a0 + ((D - D1) / (3 * D)) • a1 + ((D - D2) / (3 * D)) • a2 +
      ((D - D3) / (3 * D)) • a3, convex_comb4 hKconv ha0 ha1 ha2 ha3 hw0 hw1 hw2 hw3 hws, ?_⟩
    have hcoord : ∀ (x0 x1 x2 x3 y : ℝ), D * y = D0 * x0 + D1 * x1 + D2 * x2 + D3 * x3 →
        (1 / 4 : ℝ) * (x0 + x1 + x2 + x3) - y = 3 * ((D - D0) / (3 * D) * x0 +
          (D - D1) / (3 * D) * x1 + (D - D2) / (3 * D) * x2 + (D - D3) / (3 * D) * x3 -
            (1 / 4 : ℝ) * (x0 + x1 + x2 + x3)) := by
      intro x0 x1 x2 x3 y hy
      have h1 : 3 * ((D - D0) / (3 * D) * x0 + (D - D1) / (3 * D) * x1 +
          (D - D2) / (3 * D) * x2 + (D - D3) / (3 * D) * x3) =
          (D * (x0 + x1 + x2 + x3) - (D0 * x0 + D1 * x1 + D2 * x2 + D3 * x3)) * D⁻¹ := by
        field_simp
        ring
      have h2 : (D * (x0 + x1 + x2 + x3) - (D0 * x0 + D1 * x1 + D2 * x2 + D3 * x3)) * D⁻¹ =
          (x0 + x1 + x2 + x3) - y := by
        rw [← hy]
        field_simp
        try ring
      rw [mul_sub, h1, h2]
      ring
    apply space_ext3
    · simp only [hg, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact hcoord _ _ _ _ _ (tdet_cramer0 a0 a1 a2 a3 q)
    · simp only [hg, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact hcoord _ _ _ _ _ (tdet_cramer1 a0 a1 a2 a3 q)
    · simp only [hg, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact hcoord _ _ _ _ _ (tdet_cramer2 a0 a1 a2 a3 q)
  -- the inclusion into a homothetic copy of `K`
  have hincl : W + t • (W - W) ⊆ AffineMap.homothety g (1 + 4 * t) '' K := by
    rintro _ ⟨w, hw, _, ⟨d, ⟨w1, hw1, w2, hw2, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨q2, hq2, hq2e⟩ := hrefl w2 (hWK hw2)
    have hs : 0 < 1 + 4 * t := by linarith
    set k : Space := (1 / (1 + 4 * t)) • w + (t / (1 + 4 * t)) • w1 +
      (3 * t / (1 + 4 * t)) • q2 with hk
    have hs' : (1 + 4 * t) ≠ 0 := hs.ne'
    have hkK : k ∈ K := by
      have h4 := convex_comb4 hKconv (hWK hw) (hWK hw1) hq2 hq2
        (w0 := 1 / (1 + 4 * t)) (w1 := t / (1 + 4 * t)) (w2 := 3 * t / (1 + 4 * t)) (w3 := 0)
        (by positivity) (by positivity) (by positivity) le_rfl (by field_simp; ring)
      simpa [hk] using h4
    refine ⟨k, hkK, ?_⟩
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    have hw2' : w2 = g - (3 : ℝ) • (q2 - g) := by rw [← hq2e]; abel
    rw [hw2', hk]
    apply space_ext3 <;>
      (simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
       field_simp
       ring)
  have hvolK : volume K ≤ volume W := by
    calc volume K = volume (W ∪ frontier W) := by rw [hKdef, closure_eq_self_union_frontier]
      _ ≤ volume W + volume (frontier W) := measure_union_le _ _
      _ = volume W := by rw [hW.addHaar_frontier volume, add_zero]
  calc volume (W + t • (W - W)) ≤ volume (AffineMap.homothety g (1 + 4 * t) '' K) :=
        measure_mono hincl
    _ = ENNReal.ofReal (|(1 + 4 * t) ^ Module.finrank ℝ Space|) * volume K :=
        Measure.addHaar_image_homothety volume g (1 + 4 * t) K
    _ ≤ ENNReal.ofReal ((1 + 4 * t) ^ 3) * volume W := by
        rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]
        gcongr

end WangZahlLot.Obl.wz_intermediate_twist_normalization
