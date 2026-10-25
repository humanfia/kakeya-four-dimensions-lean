-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Local.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Slab
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Classes
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Grid
import Submission.WZ.Obl.wz_finite_shading_second_moment
import Submission.WZ.Obl.wz_tube_packing_bound

/-!
# Local transverse filling (Wang–Zahl, Lemma 5.10, localised to a `b`-ball)

Let `P₀` be an `a × b × 1/1000` prism with shading `H₀`, and `x ∈ H₀` a point at which `H₀` is
`h`-dense in `P₀ ∩ B(x, b)`. Suppose every point of `H₀` lies in the shading `H i` of a prism
`P i` (same dimensions) whose normal makes projective angle `≥ θ` with the normal `e₀` of `P₀`,
the shadings `H i` being `h`-dense in `P i ∩ B(y, b)` around each of their points `y`. Then the
union of the shadings fills `B(x, 2b)` to the extent `≳ h³ θ⁴ b³ / (1 + log (b / a))`.

Proof (Córdoba-type `L²` argument):
1. `Y := H₀ ∩ B(x, b)` has volume `≥ h a b² / 8`.
2. Pigeonhole the sign-normalised normals of the transverse prisms into `O(θ⁻³)` classes of
   diameter `≤ θ / 4`; one class `K'` covers `Y' ⊆ Y` with `|Y'| ≳ θ³ |Y|`.
3. For a member normal `n*` of the class, `n* = α e₀ + σ v` with `v ⊥ e₀` unit and `σ ≥ θ / 2`;
   complete `(e₀, w, v)` to a frame. Every normal `ñ` of the class has `⟪ñ, v⟫ ≥ θ / 4`.
4. Grid `P₀ ∩ B(x, b)` by `⌊⟪w, q - x⟫ / a⌋` and `⌊⟪v, q - x⟫ / Δ⌋`, `Δ = 32 a / θ`; cells have
   volume `≤ 2 a² Δ`. Pigeonhole a row (fixed `w`-index) with many cells meeting `Y'`, keep the
   cells of one parity, and pick a point `y_j ∈ Y'` in each: `N ≳ |Y'| / (a b Δ)` points.
5. `Z_j := H i_j ∩ B(y_j, b)` (with `y_j ∈ H i_j`, `i_j ∈ K'`) has `|Z_j| ≥ h a b² / 8`, and
   `|Z_j ∩ Z_j'| ≲ a b² / |j - j'|` by `inner_sep_of_meet` and `two_slab_volume_le`.
6. Summing (harmonic numbers) and `wz_finite_shading_second_moment` conclude.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- A regular shading has volume at least `h a b² / 8` in the `b`-ball around each of its
points. -/
theorem loc_regular_lower {a b h : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 ≤ h) {c : Space} {u : Fin 3 → Space} (hu : Orthonormal ℝ u) {H : Set Space}
    {p : Space} (hp : p ∈ prism a b c u)
    (hreg : ENNReal.ofReal h * volume (prism a b c u ∩ ball p b) ≤ volume (H ∩ ball p b)) :
    ENNReal.ofReal (h * a * b ^ 2 / 8) ≤ volume (H ∩ ball p b) := by
  have hb0 : 0 < b := ha.trans_le hab
  have h1 := volume_prism_inter_ball_ge ha.le hb0.le hu hp hb0
  have e1 : a / 2 ≤ min a (b / 2) := le_min (by linarith) (by linarith)
  have e2 : min b (b / 2) = b / 2 := min_eq_right (by linarith)
  have e3 : min (1 / 1000 : ℝ) (b / 2) = b / 2 := min_eq_right (by linarith)
  rw [e2, e3] at h1
  calc ENNReal.ofReal (h * a * b ^ 2 / 8)
      = ENNReal.ofReal h * ENNReal.ofReal (a / 2 * (b / 2) * (b / 2)) := by
        rw [← ENNReal.ofReal_mul hh]; congr 1; ring
    _ ≤ ENNReal.ofReal h * ENNReal.ofReal (min a (b / 2) * (b / 2) * (b / 2)) := by
        gcongr
    _ ≤ ENNReal.ofReal h * volume (prism a b c u ∩ ball p b) := by gcongr
    _ ≤ volume (H ∩ ball p b) := hreg

/-- Two points of a prism are `2a`-close along the (sign-normalised) normal. -/
theorem loc_slab_of_prism {a b : ℝ} {c : Space} {u : Fin 3 → Space} {p q : Space}
    (hp : p ∈ prism a b c u) (hq : q ∈ prism a b c u) :
    |inner ℝ (sgnNormal (u 0)) (q - p)| ≤ 2 * a := by
  rw [abs_inner_sgnNormal]
  have e : q - p = (q - c) - (p - c) := by abel
  rw [e, inner_sub_right]
  have h1 := abs_le.mp hp.1
  have h2 := abs_le.mp hq.1
  rw [abs_le]; constructor <;> linarith

/-- Lower bound for an inner product through the frame expansion. -/
theorem loc_frame_lower {a θ : ℝ} {e₀ w v n d : Space} (hframe : Orthonormal ℝ ![e₀, w, v])
    (hn : ‖n‖ = 1) (hv : θ / 4 ≤ inner ℝ n v) (he : |inner ℝ e₀ d| ≤ 2 * a)
    (hw : |inner ℝ w d| ≤ a) :
    |inner ℝ v d| * (θ / 4) - 3 * a ≤ |inner ℝ n d| := by
  have hd := eq_sum_frame hframe d
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hd
  have hnd : inner ℝ n d = inner ℝ e₀ d * inner ℝ n e₀ + inner ℝ w d * inner ℝ n w +
      inner ℝ v d * inner ℝ n v := by
    conv_lhs => rw [hd]
    simp only [inner_add_right, inner_smul_right]
  have he0 : ‖e₀‖ = 1 := by simpa using hframe.1 0
  have hw0 : ‖w‖ = 1 := by simpa using hframe.1 1
  have h1 : |inner ℝ n e₀| ≤ 1 := by
    have := abs_real_inner_le_norm n e₀
    rwa [hn, he0, one_mul] at this
  have h2 : |inner ℝ n w| ≤ 1 := by
    have := abs_real_inner_le_norm n w
    rwa [hn, hw0, one_mul] at this
  have ha0 : 0 ≤ a := by linarith [abs_nonneg (inner ℝ w d)]
  have hA : |inner ℝ e₀ d * inner ℝ n e₀| ≤ 2 * a := by
    rw [abs_mul]
    calc |inner ℝ e₀ d| * |inner ℝ n e₀| ≤ 2 * a * 1 :=
          mul_le_mul he h1 (abs_nonneg _) (by linarith)
      _ = 2 * a := mul_one _
  have hB : |inner ℝ w d * inner ℝ n w| ≤ a := by
    rw [abs_mul]
    calc |inner ℝ w d| * |inner ℝ n w| ≤ a * 1 :=
          mul_le_mul hw h2 (abs_nonneg _) ha0
      _ = a := mul_one _
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  rw [hnd]
  rcases le_total 0 (inner ℝ v d) with hC | hC
  · rw [abs_of_nonneg hC]
    have : inner ℝ v d * (θ / 4) ≤ inner ℝ v d * inner ℝ n v :=
      mul_le_mul_of_nonneg_left hv hC
    have := le_abs_self (inner ℝ e₀ d * inner ℝ n e₀ + inner ℝ w d * inner ℝ n w +
      inner ℝ v d * inner ℝ n v)
    linarith
  · rw [abs_of_nonpos hC]
    have : inner ℝ v d * inner ℝ n v ≤ inner ℝ v d * (θ / 4) :=
      mul_le_mul_of_nonpos_left hv hC
    have := neg_abs_le (inner ℝ e₀ d * inner ℝ n e₀ + inner ℝ w d * inner ℝ n w +
      inner ℝ v d * inner ℝ n v)
    linarith

/-- Sum of `1 / d` over a finset of naturals in `[1, M]`. -/
theorem loc_sum_inv_nat_le (S : Finset ℕ) (M : ℕ) (hS : ∀ d ∈ S, 1 ≤ d ∧ d ≤ M) :
    ∑ d ∈ S, (1 / (d : ℝ)) ≤ 1 + Real.log M := by
  calc ∑ d ∈ S, (1 / (d : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 M, (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd; rw [Finset.mem_Icc]; exact hS d hd
        · intro d _ _; positivity
    _ = (harmonic M : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1 + Real.log M := harmonic_le_one_add_log M

/-- Second moment bound, indexed by a finset of integers. -/
theorem loc_second_moment (J : Finset ℤ) (Z : ℤ → Set Space) (E : Set Space) (u A : ℝ)
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) (hZ : ∀ j ∈ J, MeasurableSet (Z j))
    (hsub : ∀ j ∈ J, Z j ⊆ E) (hu : 0 ≤ u) (hA : 0 < A)
    (hlu : ∀ j ∈ J, u ≤ (volume (Z j)).toReal)
    (hrow : ∀ j ∈ J, ∑ j' ∈ J, (volume (Z j ∩ Z j')).toReal ≤ A) :
    u ^ 2 * (J.card : ℝ) ≤ A * (volume E).toReal := by
  classical
  let g : Fin J.card → ℤ := fun k => (J.equivFin.symm k : ℤ)
  have hg : ∀ k, g k ∈ J := fun k => (J.equivFin.symm k).2
  have hsum : ∀ f : ℤ → ℝ, ∑ k : Fin J.card, f (g k) = ∑ j ∈ J, f j := by
    intro f
    rw [← Finset.sum_coe_sort J f]
    exact Equiv.sum_comp J.equivFin.symm (fun x => f x)
  have key := WangZahlLot.wz_finite_shading_second_moment J.card Finset.univ (fun k => Z (g k))
    E u A hE hEfin (fun k _ => hZ _ (hg k)) (fun k _ => hsub _ (hg k)) hu hA
    (fun k _ => hlu _ (hg k))
    (fun k _ => by
      rw [hsum (fun j' => (volume (Z (g k) ∩ Z j')).toReal)]
      exact hrow _ (hg k))
  simpa using key

/-- The final arithmetic. -/
theorem loc_final_arith {a b h θ m V L : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hθ : 0 < θ) (hL : 0 < L) (hV : 0 ≤ V)
    (hJ : h * a * b ^ 2 / 8 * (θ ^ 3 / 100000) ≤ 20 * a * b * (32 * a / θ) * m)
    (hmom : (h * a * b ^ 2 / 8) ^ 2 * m ≤ 10000 * a * b ^ 2 * L * V) :
    1 / 10 ^ 15 * h ^ 3 * θ ^ 4 * b ^ 3 / L ≤ V := by
  have hJ1 : h * a * b ^ 2 / 8 * (θ ^ 3 / 100000) * θ ≤ 640 * a ^ 2 * b * m := by
    have e : 20 * a * b * (32 * a / θ) * m = 640 * a ^ 2 * b * m / θ := by
      field_simp; ring
    rw [e, le_div_iff₀ hθ] at hJ
    exact hJ
  have hJ' : h * b * θ ^ 4 ≤ 512000000 * a * m := by
    have key : (a * b) * (h * b * θ ^ 4) ≤ (a * b) * (512000000 * a * m) := by
      have e1 : (a * b) * (h * b * θ ^ 4) =
          (h * a * b ^ 2 / 8 * (θ ^ 3 / 100000) * θ) * 800000 := by ring
      have e2 : (a * b) * (512000000 * a * m) = (640 * a ^ 2 * b * m) * 800000 := by ring
      rw [e1, e2]; linarith
    exact le_of_mul_le_mul_left key (mul_pos ha hb)
  have P0 : 0 ≤ h ^ 2 * a ^ 2 * b ^ 4 / 64 := by positivity
  have s1 := mul_le_mul_of_nonneg_left hJ' P0
  have s3 := mul_le_mul_of_nonneg_left hmom (by positivity : (0 : ℝ) ≤ 512000000 * a)
  have s4 : (a ^ 2 * b ^ 2) * (h ^ 3 * b ^ 3 * θ ^ 4) ≤
      (a ^ 2 * b ^ 2) * (327680000000000 * L * V) := by
    have e1 : (a ^ 2 * b ^ 2) * (h ^ 3 * b ^ 3 * θ ^ 4) =
        64 * (h ^ 2 * a ^ 2 * b ^ 4 / 64 * (h * b * θ ^ 4)) := by ring
    have e2 : (a ^ 2 * b ^ 2) * (327680000000000 * L * V) =
        64 * (512000000 * a * (10000 * a * b ^ 2 * L * V)) := by ring
    have e3 : h ^ 2 * a ^ 2 * b ^ 4 / 64 * (512000000 * a * m) =
        512000000 * a * ((h * a * b ^ 2 / 8) ^ 2 * m) := by ring
    rw [e1, e2]
    linarith
  have s5 := le_of_mul_le_mul_left s4 (by positivity)
  rw [div_le_iff₀ hL]
  nlinarith [mul_nonneg hL.le hV]
/-- Sum of `1 / |j - j'|` over `j' ∈ J \ {j}`. -/
theorem loc_sum_inv_abs_le (J : Finset ℤ) (j : ℤ) (X : ℝ) (hX : 1 ≤ X)
    (hM : ∀ j' ∈ J, |(j : ℝ) - j'| ≤ X) :
    ∑ j' ∈ J.erase j, 1 / |(j : ℝ) - j'| ≤ 2 * (1 + Real.log X) := by
  classical
  set M := ⌊X⌋₊ with hM_def
  have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hMpos : 0 < M := Nat.floor_pos.mpr hX
  have hlog : Real.log M ≤ Real.log X := Real.log_le_log (by exact_mod_cast hMpos) hMX
  have hcast : ∀ j' : ℤ, |(j : ℝ) - j'| = (((j - j').natAbs : ℕ) : ℝ) := by
    intro j'
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  have hle : ∀ j' ∈ J, (j - j').natAbs ≤ M := by
    intro j' hj'
    apply Nat.le_floor
    rw [← hcast]
    exact hM j' hj'
  have key : ∀ T : Finset ℤ, T ⊆ J.erase j → Set.InjOn (fun j' => (j - j').natAbs) T →
      ∑ j' ∈ T, 1 / |(j : ℝ) - j'| ≤ 1 + Real.log M := by
    intro T hT hinj
    rw [Finset.sum_congr rfl (fun j' _ => by rw [hcast j']),
      ← Finset.sum_image (f := fun d : ℕ => 1 / (d : ℝ)) hinj]
    apply loc_sum_inv_nat_le
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨j', hj', rfl⟩ := hd
    have hj'2 := Finset.mem_erase.mp (hT hj')
    constructor
    · have : j - j' ≠ 0 := sub_ne_zero.mpr (Ne.symm hj'2.1)
      exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr this)
    · exact hle j' hj'2.2
  rw [← Finset.sum_filter_add_sum_filter_not (J.erase j) (fun j' => j < j')]
  have h1 := key ((J.erase j).filter (fun j' => j < j')) (Finset.filter_subset _ _) ?_
  have h2 := key ((J.erase j).filter (fun j' => ¬ j < j')) (Finset.filter_subset _ _) ?_
  · linarith
  · intro j₁ hj₁ j₂ hj₂ he
    rw [Finset.mem_coe, Finset.mem_filter] at hj₁ hj₂
    simp only at he
    omega
  · intro j₁ hj₁ j₂ hj₂ he
    rw [Finset.mem_coe, Finset.mem_filter] at hj₁ hj₂
    simp only at he
    omega

/-- The overlap of two shadings through separated points of the grid. -/
theorem loc_pair_bound {a b θ k : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {e₀ w v n₁ n₂ y₁ y₂ : Space} (hframe : Orthonormal ℝ ![e₀, w, v])
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1) (hv₁ : θ / 4 ≤ inner ℝ n₁ v) (hs : ‖n₁ - n₂‖ ≤ θ / 4)
    (he : |inner ℝ e₀ (y₂ - y₁)| ≤ 2 * a) (hw : |inner ℝ w (y₂ - y₁)| ≤ a)
    (hk : 2 ≤ k) (hvv : k * (32 * a / θ) / 2 ≤ |inner ℝ v (y₂ - y₁)|)
    (hy : ‖y₂ - y₁‖ ≤ 2 * b) (S : Set Space)
    (hS : S ⊆ {q | |inner ℝ n₁ (q - y₁)| ≤ 2 * a} ∩ {q | |inner ℝ n₂ (q - y₂)| ≤ 2 * a} ∩
      ball y₁ b) :
    volume S ≤ ENNReal.ofReal (768 * a * b ^ 2 / k) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨q, hq⟩
  · simp [hSe]
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hS hq
  have hq3' : ‖q - y₁‖ ≤ b := by rw [mem_ball, dist_eq_norm] at hq3; exact hq3.le
  have hsep := inner_sep_of_meet hq1 hq2 hq3'
  have hlow := loc_frame_lower hframe hn₁ hv₁ he hw
  have hb0 : 0 < b := ha.trans_le hab
  have hs0 : 0 ≤ ‖n₁ - n₂‖ := norm_nonneg _
  have hvθ : k * (32 * a / θ) / 2 * (θ / 4) = 4 * a * k := by field_simp; ring
  have hlow' : 4 * a * k - 3 * a ≤ |inner ℝ n₁ (y₂ - y₁)| := by
    have := mul_le_mul_of_nonneg_right hvv (by linarith : (0:ℝ) ≤ θ / 4)
    linarith
  have hsb : ‖n₁ - n₂‖ * (b + ‖y₂ - y₁‖) ≤ ‖n₁ - n₂‖ * (3 * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hk2 : 0 ≤ a * (k - 2) := mul_nonneg ha.le (by linarith)
  have hkey : a * k ≤ 6 * b * ‖n₁ - n₂‖ := by nlinarith
  have hspos : 0 < ‖n₁ - n₂‖ := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hkey
      nlinarith
  have hs1 : ‖n₁ - n₂‖ ≤ 1 := by linarith
  have h2 := two_slab_volume_le (y₁ := y₁) (y₂ := y₂) hn₁ hn₂
    (by linarith : (0:ℝ) ≤ 2 * a) hb0.le hspos hs1
  calc volume S ≤ volume ({q | |inner ℝ n₁ (q - y₁)| ≤ 2 * a} ∩
        {q | |inner ℝ n₂ (q - y₂)| ≤ 2 * a} ∩ ball y₁ b) := measure_mono hS
    _ ≤ ENNReal.ofReal (32 * (2 * a) ^ 2 * b / ‖n₁ - n₂‖) := h2
    _ ≤ ENNReal.ofReal (768 * a * b ^ 2 / k) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_div_iff₀ hspos (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 128 * a * b)]
/-- Row sums of the overlap matrix of the shadings through the selected points. -/
theorem loc_row_bound {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {e₀ w v : Space} (hframe : Orthonormal ℝ ![e₀, w, v])
    (J : Finset ℤ) (y nrm : ℤ → Space) (Z : ℤ → Set Space)
    (hnrm : ∀ j ∈ J, ‖nrm j‖ = 1) (hv : ∀ j ∈ J, θ / 4 ≤ inner ℝ (nrm j) v)
    (hdiam : ∀ j ∈ J, ∀ j' ∈ J, ‖nrm j - nrm j'‖ ≤ θ / 4)
    (hslab : ∀ j ∈ J, Z j ⊆ {q | |inner ℝ (nrm j) (q - y j)| ≤ 2 * a} ∩ ball (y j) b)
    (he : ∀ j ∈ J, ∀ j' ∈ J, |inner ℝ e₀ (y j' - y j)| ≤ 2 * a)
    (hball : ∀ j ∈ J, ∀ j' ∈ J, ‖y j' - y j‖ ≤ 2 * b)
    (hpair : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
        |inner ℝ w (y j - y j')| < a ∧
        (|(j : ℝ) - j'|) * (32 * a / θ) / 2 ≤ |inner ℝ v (y j - y j')| ∧ 2 ≤ |(j : ℝ) - j'|)
    (hbound : ∀ j ∈ J, |(j : ℝ)| ≤ b / (32 * a / θ) + 1) :
    ∀ j ∈ J, ∑ j' ∈ J, (volume (Z j ∩ Z j')).toReal ≤
      10000 * a * b ^ 2 * (1 + Real.log (b / a)) := by
  intro j hj
  have hb0 : 0 < b := ha.trans_le hab
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have hlogba : 0 ≤ Real.log (b / a) := Real.log_nonneg hba
  -- the diagonal term
  have hdiag : (volume (Z j ∩ Z j)).toReal ≤ 16 * a * b ^ 2 := by
    rw [Set.inter_self]
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    calc volume (Z j) ≤ volume ({q | |inner ℝ (nrm j) (q - y j)| ≤ 2 * a} ∩ ball (y j) b) :=
          measure_mono (hslab j hj)
      _ ≤ ENNReal.ofReal (8 * (2 * a) * b ^ 2) :=
          slab_ball_volume_le (hnrm j hj) (by linarith) hb0.le
      _ = ENNReal.ofReal (16 * a * b ^ 2) := by ring_nf
  -- the off-diagonal terms
  have hoff : ∀ j' ∈ J.erase j, (volume (Z j ∩ Z j')).toReal ≤
      768 * a * b ^ 2 * (1 / |(j : ℝ) - j'|) := by
    intro j' hj'
    obtain ⟨hne, hj'J⟩ := Finset.mem_erase.mp hj'
    obtain ⟨hw', hv', hk'⟩ := hpair j' hj'J j hj hne
    have hk : 2 ≤ |(j : ℝ) - j'| := by rw [abs_sub_comm]; exact hk'
    have hvv : |(j : ℝ) - j'| * (32 * a / θ) / 2 ≤ |inner ℝ v (y j' - y j)| := by
      rw [abs_sub_comm (j : ℝ)]; exact hv'
    have hS : Z j ∩ Z j' ⊆ {q | |inner ℝ (nrm j) (q - y j)| ≤ 2 * a} ∩
        {q | |inner ℝ (nrm j') (q - y j')| ≤ 2 * a} ∩ ball (y j) b := by
      intro q ⟨hq1, hq2⟩
      exact ⟨⟨(hslab j hj hq1).1, (hslab j' hj'J hq2).1⟩, (hslab j hj hq1).2⟩
    have := loc_pair_bound ha hab hθ hθ1 hframe (hnrm j hj) (hnrm j' hj'J) (hv j hj)
      (hdiam j hj j' hj'J) (he j hj j' hj'J) hw'.le hk hvv (hball j hj j' hj'J) _ hS
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    convert this using 2
    ring
  -- the harmonic sum
  have hX : ∀ j' ∈ J, |(j : ℝ) - j'| ≤ 4 * (b / a) := by
    intro j' hj'
    have h1 := hbound j hj
    have h2 := hbound j' hj'
    have hΔ : b / (32 * a / θ) ≤ b / a := by
      apply div_le_div_of_nonneg_left hb0.le ha
      rw [le_div_iff₀ hθ]; nlinarith
    calc |(j : ℝ) - j'| ≤ |(j : ℝ)| + |(j' : ℝ)| := abs_sub _ _
      _ ≤ 4 * (b / a) := by linarith
  have hsum := loc_sum_inv_abs_le J j (4 * (b / a)) (by linarith) hX
  have hlog4 : Real.log (4 * (b / a)) ≤ 3 + Real.log (b / a) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  rw [← Finset.add_sum_erase J _ hj]
  have hab2 : 0 < a * b ^ 2 := by positivity
  calc (volume (Z j ∩ Z j)).toReal + ∑ j' ∈ J.erase j, (volume (Z j ∩ Z j')).toReal
      ≤ 16 * a * b ^ 2 + ∑ j' ∈ J.erase j, 768 * a * b ^ 2 * (1 / |(j : ℝ) - j'|) :=
        add_le_add hdiag (Finset.sum_le_sum hoff)
    _ = 16 * a * b ^ 2 + 768 * a * b ^ 2 * ∑ j' ∈ J.erase j, 1 / |(j : ℝ) - j'| := by
        rw [Finset.mul_sum]
    _ ≤ 16 * a * b ^ 2 + 768 * a * b ^ 2 * (2 * (1 + Real.log (4 * (b / a)))) := by
        gcongr
    _ ≤ 10000 * a * b ^ 2 * (1 + Real.log (b / a)) := by
        nlinarith [mul_le_mul_of_nonneg_left hlog4 hab2.le, mul_nonneg hab2.le hlogba]
/-- Local transverse filling. -/
theorem local_filling : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : Finset (Fin n)) (a b h θ : ℝ)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space) (H : Fin n → Set Space)
    (c₀ : Space) (u₀ : Fin 3 → Space) (H₀ : Set Space) (x : Space),
    0 < a → a ≤ b → b ≤ 1 / 1000000 → 0 < h → h ≤ 1 → 0 < θ → θ ≤ 1 →
    (∀ i ∈ K, Orthonormal ℝ (u i)) → (∀ i ∈ K, MeasurableSet (H i)) →
    (∀ i ∈ K, H i ⊆ prism a b (c i) (u i)) →
    (∀ i ∈ K, ∀ p ∈ H i, ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p b) ≤
      volume (H i ∩ ball p b)) →
    Orthonormal ℝ u₀ → H₀ ⊆ prism a b c₀ u₀ → x ∈ H₀ →
    ENNReal.ofReal h * volume (prism a b c₀ u₀ ∩ ball x b) ≤ volume (H₀ ∩ ball x b) →
    (∀ y ∈ H₀, ∃ i ∈ K, y ∈ H i ∧ θ ≤ pd (u i 0) (u₀ 0)) →
    ENNReal.ofReal (C * h ^ 3 * θ ^ 4 * b ^ 3 / (1 + Real.log (b / a))) ≤
      volume (ball x (2 * b) ∩ ⋃ i ∈ K, H i) := by
  refine ⟨1 / 10 ^ 15, by norm_num, ?_⟩
  intro n K a b h θ c u H c₀ u₀ H₀ x ha hab hb hh hh1 hθ hθ1 hu hHm hHsub hHreg hu₀ hH₀sub hx
    hH₀reg htrans
  classical
  have hb0 : 0 < b := ha.trans_le hab
  -- Step 1: `H₀ ∩ B(x, b)` is large
  have hY : ENNReal.ofReal (h * a * b ^ 2 / 8) ≤ volume (H₀ ∩ ball x b) :=
    loc_regular_lower ha hab hb hh.le hu₀ (hH₀sub hx) hH₀reg
  -- Step 2: one class of transverse normals covers a large part of it
  have hYKT : H₀ ∩ ball x b ⊆ ⋃ i ∈ K.filter (fun i => θ ≤ pd (u i 0) (u₀ 0)), H i := by
    intro y hy
    obtain ⟨i, hiK, hyi, hθi⟩ := htrans y hy.1
    exact Set.mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hiK, hθi⟩) hyi
  obtain ⟨K', hK'KT, hK'diam, hK'vol⟩ := normal_class_pigeonhole
    (K.filter (fun i => θ ≤ pd (u i 0) (u₀ 0))) (fun i => u i 0)
    (fun i hi => (hu i (Finset.mem_filter.mp hi).1).1 0) H (H₀ ∩ ball x b) hYKT hθ hθ1
  have hK'K : ∀ i ∈ K', i ∈ K := fun i hi => (Finset.mem_filter.mp (hK'KT hi)).1
  have hK'θ : ∀ i ∈ K', θ ≤ pd (u i 0) (u₀ 0) := fun i hi =>
    (Finset.mem_filter.mp (hK'KT hi)).2
  have hY'vol : ENNReal.ofReal (h * a * b ^ 2 / 8 * (θ ^ 3 / 100000)) ≤
      volume (H₀ ∩ ball x b ∩ ⋃ i ∈ K', H i) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (h * a * b ^ 2 / 8) * ENNReal.ofReal (θ ^ 3 / 100000)
        ≤ volume (H₀ ∩ ball x b) * ENNReal.ofReal (θ ^ 3 / 100000) := by gcongr
      _ ≤ _ := hK'vol
  have hY'pos : volume (H₀ ∩ ball x b ∩ ⋃ i ∈ K', H i) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hY'vol).ne'
  obtain ⟨y₀, hy₀⟩ := nonempty_of_measure_ne_zero hY'pos
  obtain ⟨istar, histar, -⟩ := Set.mem_iUnion₂.mp hy₀.2
  -- Step 3: a good direction `v ⊥ e₀` for the class, and a frame `(e₀, w, v)`
  have he₀ : ‖u₀ 0‖ = 1 := hu₀.1 0
  have hnu : ∀ i ∈ K', ‖sgnNormal (u i 0)‖ = 1 := fun i hi => by
    rw [norm_sgnNormal]; exact (hu i (hK'K i hi)).1 0
  obtain ⟨v, hv1, he₀v, hvθ⟩ := exists_good_direction he₀ (hnu istar histar) hθ.le
    (by rw [pd_sgnNormal_left]; exact hK'θ istar histar)
  have hK'v : ∀ i ∈ K', θ / 4 ≤ inner ℝ (sgnNormal (u i 0)) v := by
    intro i hi
    have hd := hK'diam istar histar i hi
    have h1 : inner ℝ (sgnNormal (u istar 0) - sgnNormal (u i 0)) v ≤
        ‖sgnNormal (u istar 0) - sgnNormal (u i 0)‖ * ‖v‖ := real_inner_le_norm _ _
    rw [inner_sub_left, hv1, mul_one] at h1
    linarith
  obtain ⟨w, hframe⟩ := exists_frame he₀ hv1 he₀v
  -- Step 4: selecting separated points along `v`
  have hΔ : a ≤ 32 * a / θ := by rw [le_div_iff₀ hθ]; nlinarith
  have hY'sub : H₀ ∩ ball x b ∩ ⋃ i ∈ K', H i ⊆ prism a b c₀ u₀ ∩ ball x b :=
    fun y hy => ⟨hH₀sub hy.1.1, hy.1.2⟩
  obtain ⟨J, y, hyY', hJvol, hJpair, hJbound⟩ :=
    grid_selection ha hab hΔ hu₀ hframe _ hY'sub
  -- Step 5: the shadings through the selected points
  have hchoice : ∀ j : ℤ, ∃ i : Fin n, j ∈ J → (i ∈ K' ∧ y j ∈ H i) := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hyY' j hj).2
      exact ⟨i, fun _ => ⟨hi, hyi⟩⟩
    · exact ⟨istar, fun h => absurd h hj⟩
  choose ι hι using hchoice
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have hL : 0 < 1 + Real.log (b / a) := by have := Real.log_nonneg hba; linarith
  set Z : ℤ → Set Space := fun j => H (ι j) ∩ ball (y j) b with hZ_def
  set E := ⋃ j ∈ J, Z j with hE_def
  have hEsub : E ⊆ ball x (2 * b) ∩ ⋃ i ∈ K, H i := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := Set.mem_iUnion₂.mp hq
    refine ⟨?_, Set.mem_iUnion₂_of_mem (hK'K _ (hι j hj).1) hqj.1⟩
    have h1 := (hyY' j hj).1.2
    have h2 := hqj.2
    rw [mem_ball] at h1 h2 ⊢
    calc dist q x ≤ dist q (y j) + dist (y j) x := dist_triangle _ _ _
      _ < b + b := add_lt_add h2 h1
      _ = 2 * b := by ring
  have hEfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hEsub.trans inter_subset_left))
  have hZm : ∀ j ∈ J, MeasurableSet (Z j) := fun j hj =>
    (hHm _ (hK'K _ (hι j hj).1)).inter measurableSet_ball
  have hEm : MeasurableSet E := Finset.measurableSet_biUnion J hZm
  have hZsub : ∀ j ∈ J, Z j ⊆ E := fun j hj q hq => Set.mem_iUnion₂_of_mem hj hq
  have hlu : ∀ j ∈ J, h * a * b ^ 2 / 8 ≤ (volume (Z j)).toReal := by
    intro j hj
    have hi := hK'K _ (hι j hj).1
    have := loc_regular_lower ha hab hb hh.le (hu _ hi) (hHsub _ hi (hι j hj).2)
      (hHreg _ hi _ (hι j hj).2)
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top hEfin (measure_mono (hZsub j hj)))).mp this
  have hslab : ∀ j ∈ J, Z j ⊆
      {q | |inner ℝ (sgnNormal (u (ι j) 0)) (q - y j)| ≤ 2 * a} ∩ ball (y j) b := by
    intro j hj q hq
    have hi := hK'K _ (hι j hj).1
    exact ⟨loc_slab_of_prism (hHsub _ hi (hι j hj).2) (hHsub _ hi hq.1), hq.2⟩
  have he : ∀ j ∈ J, ∀ j' ∈ J, |inner ℝ (u₀ 0) (y j' - y j)| ≤ 2 * a := by
    intro j hj j' hj'
    have := loc_slab_of_prism (hH₀sub (hyY' j hj).1.1) (hH₀sub (hyY' j' hj').1.1)
    rwa [abs_inner_sgnNormal] at this
  have hball : ∀ j ∈ J, ∀ j' ∈ J, ‖y j' - y j‖ ≤ 2 * b := by
    intro j hj j' hj'
    have h1 := (hyY' j hj).1.2
    have h2 := (hyY' j' hj').1.2
    rw [mem_ball, dist_eq_norm] at h1 h2
    calc ‖y j' - y j‖ = ‖(y j' - x) - (y j - x)‖ := by congr 1; abel
      _ ≤ ‖y j' - x‖ + ‖y j - x‖ := norm_sub_le _ _
      _ ≤ 2 * b := by linarith
  -- Step 6–7: the row sums of the overlaps
  have hrow := loc_row_bound ha hab hθ hθ1 hframe J y (fun j => sgnNormal (u (ι j) 0)) Z
    (fun j hj => hnu _ (hι j hj).1) (fun j hj => hK'v _ (hι j hj).1)
    (fun j hj j' hj' => hK'diam _ (hι j hj).1 _ (hι j' hj').1) hslab he hball hJpair hJbound
  -- Step 8: the second moment bound, and the arithmetic
  have hmom := loc_second_moment J Z E (h * a * b ^ 2 / 8)
    (10000 * a * b ^ 2 * (1 + Real.log (b / a))) hEm hEfin hZm hZsub (by positivity)
    (by positivity) hlu hrow
  have hJ : h * a * b ^ 2 / 8 * (θ ^ 3 / 100000) ≤ 20 * a * b * (32 * a / θ) * J.card :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hY'vol.trans hJvol)
  have hfin := loc_final_arith ha hb0 hh hθ hL ENNReal.toReal_nonneg hJ hmom
  calc ENNReal.ofReal (1 / 10 ^ 15 * h ^ 3 * θ ^ 4 * b ^ 3 / (1 + Real.log (b / a)))
      ≤ ENNReal.ofReal (volume E).toReal := ENNReal.ofReal_le_ofReal hfin
    _ = volume E := ENNReal.ofReal_toReal hEfin
    _ ≤ volume (ball x (2 * b) ∩ ⋃ i ∈ K, H i) := measure_mono hEsub


end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
