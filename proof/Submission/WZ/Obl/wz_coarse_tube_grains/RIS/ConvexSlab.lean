-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ConvexSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# WZ Lemma 4.9: a convex set concentrated near a hyperplane lies in a proportional neighbourhood

Let `U ⊆ ℝ³` be convex with `0 < vol U < ∞`, `ν` a unit vector, and suppose a share `τ ∈ (0,1]` of
the volume of `U` lies in the slab `{|⟪ν,p⟫ - t₀| ≤ s}`. Then `U` lies in the slab of half-width
`96 s / τ`. WZ prove this with Brunn's theorem; here we use homotheties instead: if `p ∈ U` is at
distance `D` from the hyperplane, the images of `A = U ∩ slab` under the homotheties of centre `p`
and ratios `1 - 3ks/D ∈ [1/2, 1]` are pairwise disjoint (they lie in disjoint slabs), contained in
`U`, and have volume `≥ vol(A)/8`; there are more than `D/(6s)` of them.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ConvexSlab

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set

noncomputable section

/-- The closed slab of half-width `s` around the hyperplane `⟪ν,p⟫ = t₀`. -/
def slab (ν : Space) (t₀ s : ℝ) : Set Space := {p | |inner ℝ ν p - t₀| ≤ s}

theorem slab_convex (ν : Space) (t₀ s : ℝ) : Convex ℝ (slab ν t₀ s) := by
  intro x hx y hy a b ha hb hab
  simp only [slab, mem_setOf_eq] at hx hy ⊢
  have : inner ℝ ν (a • x + b • y) - t₀ = a * (inner ℝ ν x - t₀) + b * (inner ℝ ν y - t₀) := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have : t₀ = (a + b) * t₀ := by rw [hab, one_mul]
    linarith [this]
  rw [this]
  calc |a * (inner ℝ ν x - t₀) + b * (inner ℝ ν y - t₀)|
      ≤ |a * (inner ℝ ν x - t₀)| + |b * (inner ℝ ν y - t₀)| := abs_add_le _ _
    _ = a * |inner ℝ ν x - t₀| + b * |inner ℝ ν y - t₀| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * s + b * s := by gcongr
    _ = s := by rw [← add_mul, hab, one_mul]

/-- The one-sided core of the argument: no point of `U` lies at height `> 48 s/τ` above the
hyperplane. -/
theorem height_le {U : Set Space} (hU : Convex ℝ U) (hpos : 0 < volume U)
    (hfin : volume U ≠ ⊤) {ν : Space} {t₀ s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ)
    (hconc : ENNReal.ofReal τ * volume U ≤ volume (U ∩ slab ν t₀ s))
    {p : Space} (hp : p ∈ U) : inner ℝ ν p - t₀ ≤ 48 * s / τ := by
  by_contra hcon
  push Not at hcon
  set D := inner ℝ ν p - t₀ with hD
  have hDpos : 0 < D := lt_trans (by positivity) hcon
  set A := U ∩ slab ν t₀ s with hA
  have hAconv : Convex ℝ A := hU.inter (slab_convex ν t₀ s)
  -- the number of homothetic copies
  set K : ℕ := ⌊D / (6 * s)⌋₊ + 1 with hK
  have hKgt : D / (6 * s) < K := by rw [hK]; push_cast; exact Nat.lt_floor_add_one _
  have hratio : ∀ k : ℕ, k < K → 1 / 2 ≤ 1 - 3 * k * s / D := by
    intro k hk
    have hk' : (k : ℝ) ≤ D / (6 * s) := by
      have : k ≤ ⌊D / (6 * s)⌋₊ := Nat.lt_succ_iff.mp hk
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
    rw [le_div_iff₀ (by positivity)] at hk'
    have : 3 * k * s / D ≤ 1 / 2 := by
      rw [div_le_iff₀ hDpos]; nlinarith
    linarith
  let h : ℕ → Space → Space := fun k x => p + (1 - 3 * k * s / D) • (x - p)
  have himage_sub : ∀ k, k < K → h k '' A ⊆ U := by
    rintro k hk _ ⟨x, hx, rfl⟩
    have hμ := hratio k hk
    have hμ1 : 1 - 3 * k * s / D ≤ 1 := by
      have : 0 ≤ 3 * k * s / D := by positivity
      linarith
    exact hU.add_smul_sub_mem hp hx.1 ⟨by linarith, hμ1⟩
  have himage_slab : ∀ k, k < K → ∀ x ∈ A,
      |inner ℝ ν (h k x) - t₀ - 3 * k * s| ≤ s := by
    intro k hk x hx
    have hμ := hratio k hk
    have hxs : |inner ℝ ν x - t₀| ≤ s := hx.2
    have hcalc : inner ℝ ν (h k x) - t₀ - 3 * k * s =
        (1 - 3 * k * s / D) * (inner ℝ ν x - t₀) := by
      simp only [h, inner_add_right, inner_smul_right, inner_sub_right]
      field_simp
      rw [hD]
      ring
    rw [hcalc, abs_mul, abs_of_nonneg (by linarith)]
    have hμ1 : 1 - 3 * k * s / D ≤ 1 := by
      have : 0 ≤ 3 * k * s / D := by positivity
      linarith
    nlinarith [abs_nonneg (inner ℝ ν x - t₀)]
  have hdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint fun k => h k '' A := by
    intro k hk l hl hkl
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have h1 := himage_slab k (Finset.mem_range.mp hk) x hx
    have h2 := himage_slab l (Finset.mem_range.mp hl) y hy
    rw [hxy] at h2
    have hkl' : (k : ℝ) ≠ l := by exact_mod_cast hkl
    rcases lt_or_gt_of_ne hkl' with hlt | hlt
    · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
      have := abs_le.mp h1; have := abs_le.mp h2
      nlinarith
    · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
      have := abs_le.mp h1; have := abs_le.mp h2
      nlinarith
  have hvol_image : ∀ k, k < K → ENNReal.ofReal (1 / 8) * volume A ≤ volume (h k '' A) := by
    intro k hk
    have hμ := hratio k hk
    have heq : h k '' A = AffineMap.homothety p (1 - 3 * k * s / D) '' A := by
      congr 1
      funext x
      simp only [h, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      abel
    rw [heq, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    gcongr
    rw [abs_of_nonneg (by positivity)]
    calc (1 / 8 : ℝ) = (1 / 2) ^ 3 := by norm_num
      _ ≤ (1 - 3 * k * s / D) ^ 3 := by gcongr
  have hnull : ∀ k ∈ Finset.range K, NullMeasurableSet (h k '' A) volume := by
    intro k _
    apply Convex.nullMeasurableSet
    exact hAconv.affine_image (AffineMap.homothety p (1 - 3 * k * s / D)) |> fun hc => by
      have heq : h k '' A = AffineMap.homothety p (1 - 3 * k * s / D) '' A := by
        congr 1
        funext x
        simp only [h, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        abel
      rw [heq]; exact hc
  have hsum : ∑ k ∈ Finset.range K, volume (h k '' A) ≤ volume U := by
    rw [← measure_biUnion_finset₀ hdisj.aedisjoint hnull]
    exact measure_mono (Set.iUnion₂_subset fun k hk => himage_sub k (Finset.mem_range.mp hk))
  have hlow : (K : ENNReal) * (ENNReal.ofReal (1 / 8) * volume A) ≤ volume U := by
    calc (K : ENNReal) * (ENNReal.ofReal (1 / 8) * volume A)
        = ∑ _k ∈ Finset.range K, ENNReal.ofReal (1 / 8) * volume A := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range K, volume (h k '' A) :=
          Finset.sum_le_sum fun k hk => hvol_image k (Finset.mem_range.mp hk)
      _ ≤ volume U := hsum
  -- convert to reals
  have hUr : 0 < (volume U).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hconcr : τ * (volume U).toReal ≤ (volume A).toReal := by
    have := ENNReal.toReal_mono hAfin hconc
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ.le] at this
  have hlowr : (K : ℝ) * (1 / 8 * (volume A).toReal) ≤ (volume U).toReal := by
    have := ENNReal.toReal_mono hfin hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_natCast] at this
  -- `K > D/(6s) > 8/τ` contradicts `K τ / 8 ≤ 1`
  have hK8 : 8 / τ < K := by
    refine lt_trans ?_ hKgt
    rw [div_lt_div_iff₀ hτ (by positivity)]
    rw [div_lt_iff₀ hτ] at hcon
    nlinarith
  have : (K : ℝ) * (1 / 8 * (τ * (volume U).toReal)) ≤ (volume U).toReal :=
    le_trans (by gcongr) hlowr
  have hKτ : (K : ℝ) * τ / 8 ≤ 1 := by
    have h2 : (K : ℝ) * (1 / 8 * (τ * (volume U).toReal)) = (K * τ / 8) * (volume U).toReal := by
      ring
    rw [h2] at this
    exact le_of_mul_le_mul_right (by linarith) hUr
  rw [div_lt_iff₀ hτ] at hK8
  linarith

/-- **WZ Lemma 4.9.** A convex set with a `τ`-share of its volume in a slab of half-width `s`
lies in the concentric slab of half-width `48 s / τ`. -/
theorem subset_slab {U : Set Space} (hU : Convex ℝ U) (hpos : 0 < volume U)
    (hfin : volume U ≠ ⊤) {ν : Space} {t₀ s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ)
    (hconc : ENNReal.ofReal τ * volume U ≤ volume (U ∩ slab ν t₀ s)) :
    U ⊆ slab ν t₀ (48 * s / τ) := by
  intro p hp
  have h1 := height_le hU hpos hfin hs hτ hconc hp
  have hconc' : ENNReal.ofReal τ * volume U ≤ volume (U ∩ slab (-ν) (-t₀) s) := by
    have : slab (-ν) (-t₀) s = slab ν t₀ s := by
      ext q
      simp only [slab, mem_setOf_eq, inner_neg_left]
      rw [show -inner ℝ ν q - -t₀ = -(inner ℝ ν q - t₀) by ring, abs_neg]
    rw [this]; exact hconc
  have h2 := height_le hU hpos hfin hs hτ hconc' hp
  simp only [inner_neg_left] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ConvexSlab
