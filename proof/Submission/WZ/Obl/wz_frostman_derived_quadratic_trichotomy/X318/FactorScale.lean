-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FactorScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatQuantitative
import Submission.WZ.Obl.wz_convex_container_tube_packing

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FactorScale.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective)
open WangZahlLot.Obl.wz_concentrated_convex_factorization (ncard_fintype)

lemma packing_contained_in_enclosure {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (W Q : Set Space) (hQ : volume Q ≠ ⊤)
    (hsub : ∀ i, Tube δ (x i) (v i) ⊆ W → Tube δ (x i) (v i) ⊆ Q) :
    ENNReal.ofReal ((contained (fun i => Tube δ (x i) (v i)) W : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal 1000000 * (volume Q) ^ 2 := by
  classical
  let S := Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ W)
  have he : contained (fun i => Tube δ (x i) (v i)) W = S.card := by
    exact ncard_fintype _
  rw [he]
  apply WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun i => x (enumerate S i)) (fun i => v (enumerate S i)) hQ
    (fun i => hv _)
  · intro i
    exact hsub _ (Finset.mem_filter.mp (enumerate_mem S i)).2
  · intro i j hij
    exact hsep _ _ ((enumerate_injective S).ne hij)

/-- The accepted endpoint packing bound applies to all tubes in a long affine
prism, after using the unit ball to normalize its longitudinal width. -/
lemma affine_prism_packing {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (e : Space ≃ᵃⁱ[ℝ] Space) :
    (contained (fun i => Tube δ (x i) (v i))
      (e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2}) : ℝ) * δ ^ 4 ≤
        64000000 * (a * b) ^ 2 := by
  obtain ⟨c, e₁, e₂, e₃, hframe, hnorm⟩ := normalize_affine_prism a b e
  let P := Prism (min a 1) (min b 1) c e₁ e₂ e₃
  have hvol : volume P = ENNReal.ofReal (8 * min a 1 * min b 1) :=
    prism_volume (le_min ha zero_le_one) (le_min hb zero_le_one) c e₁ e₂ e₃ hframe
  have hfinite : volume P ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hpack := packing_contained_in_enclosure hδ x v hv hsep _ P hfinite
    (fun i hi y hy => hnorm ⟨hi hy, hball i hy⟩)
  rw [hvol, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)] at hpack
  have hp : _ ≤ 1000000 * (8 * min a 1 * min b 1) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hpack
  have hm : 0 ≤ min a 1 * min b 1 := by positivity
  have hma : min a 1 * min b 1 ≤ a * b :=
    mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min hb zero_le_one) ha
  calc
    _ ≤ 1000000 * (8 * min a 1 * min b 1) ^ 2 := hp
    _ = 64000000 * (min a 1 * min b 1) ^ 2 := by ring
    _ ≤ 64000000 * (a * b) ^ 2 := by gcongr

/-- Saturation and distinctness force a factor of large effective density to
have transverse area correspondingly larger than the original tube area. -/
theorem saturated_factor_scale {δ ν a b c : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hb : 0 < b)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (e : Space ≃ᵃⁱ[ℝ] Space)
    (hsat : δ ^ ν * c * a * b ≤
      (contained (fun i => Tube δ (x i) (v i))
        (e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2}) : ℝ) * δ ^ 2) :
    δ ^ ν * c * δ ^ 2 ≤ 64000000 * a * b := by
  have hp := affine_prism_packing hδ ha.le hb.le x v hv hsep hball e
  have hh := mul_le_mul_of_nonneg_right hsat (sq_nonneg δ)
  have hprod : (δ ^ ν * c * δ ^ 2) * (a * b) ≤
      (64000000 * a * b) * (a * b) := by nlinarith only [hh, hp]
  exact (mul_le_mul_iff_left₀ (mul_pos ha hb)).mp hprod

/-- Absorbing the absolute packing constant converts effective density to a
separation of the tube radius from the wide transverse scale. -/
lemma scale_separation_of_density {δ ν κ γ a b c C : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hab : a ≤ b) (hC : 0 ≤ C)
    (hc : δ ^ (-κ) ≤ c) (hscale : δ ^ ν * c * δ ^ 2 ≤ C * a * b)
    (habsorb : C * δ ^ (κ - ν - 2 * γ) ≤ 1) :
    δ ≤ δ ^ γ * b := by
  have hcoef : C * δ ^ (κ - ν) ≤ δ ^ (2 * γ) :=
    mul_rpow_le_of_absorbed hδ habsorb
  have hinv : δ ^ (κ - ν) * (δ ^ ν * δ ^ (-κ)) = 1 := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    convert Real.rpow_zero δ using 1 <;> congr 1 <;> ring
  have hsquare : δ ^ 2 ≤ (δ ^ γ * b) ^ 2 := by
    calc
      δ ^ 2 = δ ^ (κ - ν) * (δ ^ ν * δ ^ (-κ) * δ ^ 2) := by
        rw [← mul_assoc, hinv, one_mul]
      _ ≤ δ ^ (κ - ν) * (δ ^ ν * c * δ ^ 2) := by gcongr
      _ ≤ δ ^ (κ - ν) * (C * a * b) :=
        mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ (κ - ν) * (C * b * b) := by gcongr
      _ = (C * δ ^ (κ - ν)) * b ^ 2 := by ring
      _ ≤ δ ^ (2 * γ) * b ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg b)
      _ = (δ ^ γ * b) ^ 2 := by
        rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]
        congr 2
        ring
  have hnonneg : 0 ≤ δ ^ γ * b := mul_nonneg (Real.rpow_nonneg hδ.le _) hb
  nlinarith only [hsquare, hnonneg, hδ]

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
