-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Boxes of comparable volume around convex sets containing a tube

WZ (Proposition 4.6, Step 3) replaces each factoring convex set by its John ellipsoid. For convex
sets `W ⊆ ball 0 R` containing a unit `ρ`-tube we use an explicit box instead: with `p = y` and
`u₃ = w` the tube's base point and direction, take `r ∈ W` almost farthest from the line
`p + ℝ u₃`, then `s ∈ W` almost farthest from the plane through that line and `r`. The box with
axes `u₁ ⊥ u₂ = perp(r - p)/‖perp(r - p)‖ ⊥ u₃` and half-widths the two maximal distances
contains `W`, and `W` contains the parallelepiped spanned by `(p + u₃ - p)/3, (r - p)/3, (s - p)/3`
at `p`, whose volume is computed by `addHaar_parallelepiped` in the frame `(u₁, u₂, u₃)`.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

/-- The closed box of dimensions `a × b × c` centred at `z` with frame `e`. This is the set
`P a b c z e` of the proposed split (`Interfaces.P`). -/
def box (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  {p | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}

/-- The component of `x` orthogonal to the unit vector `u`. -/
def perp (u x : Space) : Space := x - inner ℝ u x • u

theorem inner_perp {u : Space} (hu : ‖u‖ = 1) (x : Space) : inner ℝ u (perp u x) = 0 := by
  simp only [perp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu]
  ring

theorem inner_perp_of_orth {u v : Space} (huv : inner ℝ v u = 0) (x : Space) :
    inner ℝ v (perp u x) = inner ℝ v x := by
  simp only [perp, inner_sub_right, inner_smul_right, huv, mul_zero, sub_zero]

theorem norm_perp_le {u : Space} (hu : ‖u‖ = 1) (x : Space) : ‖perp u x‖ ≤ ‖x‖ := by
  have hdecomp : x = perp u x + inner ℝ u x • u := by simp [perp]
  have hpu : inner ℝ (perp u x) u = 0 := by rw [real_inner_comm]; exact inner_perp hu x
  have horth : inner ℝ (perp u x) (inner ℝ u x • u) = 0 := by
    rw [inner_smul_right, hpu, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (perp u x)
    (inner ℝ u x • u) horth
  rw [← hdecomp] at h
  have h2 : ‖perp u x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖inner ℝ u x • u‖]
  nlinarith [norm_nonneg (perp u x), norm_nonneg x]

theorem abs_inner_le_norm_perp {u v : Space} (hv : ‖v‖ = 1) (huv : inner ℝ v u = 0)
    (x : Space) : |inner ℝ v x| ≤ ‖perp u x‖ := by
  rw [← inner_perp_of_orth huv x]
  calc |inner ℝ v (perp u x)| ≤ ‖v‖ * ‖perp u x‖ := abs_real_inner_le_norm _ _
    _ = ‖perp u x‖ := by rw [hv, one_mul]

/-- A function bounded on a nonempty set, exceeding `c > 0` somewhere, has a supremum `M ≥ c`
attained up to a factor `2`. -/
theorem exists_half_max {W : Set Space} (f : Space → ℝ) {B c : ℝ} (hc : 0 < c)
    (hB : ∀ x ∈ W, f x ≤ B) (hlow : ∃ x ∈ W, c ≤ f x) :
    ∃ M, c ≤ M ∧ M ≤ B ∧ (∀ x ∈ W, f x ≤ M) ∧ ∃ x ∈ W, M / 2 < f x := by
  obtain ⟨x₀, hx₀, hcx₀⟩ := hlow
  have hne : (f '' W).Nonempty := ⟨f x₀, x₀, hx₀, rfl⟩
  have hbdd : BddAbove (f '' W) := ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact hB x hx⟩
  set M := sSup (f '' W)
  have hle : ∀ x ∈ W, f x ≤ M := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hcM : c ≤ M := hcx₀.trans (hle x₀ hx₀)
  have hMB : M ≤ B := csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hB x hx)
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (by linarith : M / 2 < M)
  exact ⟨M, hcM, hMB, hle, x, hx, hlt⟩

/-- An orthonormal basis of `Space` whose last two vectors are prescribed orthonormal vectors. -/
theorem exists_frame {u₂ u₃ : Space} (h₂ : ‖u₂‖ = 1) (h₃ : ‖u₃‖ = 1)
    (h23 : inner ℝ u₂ u₃ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 1 = u₂ ∧ b 2 = u₃ := by
  let v : Fin 3 → Space := ![0, u₂, u₃]
  let s : Set (Fin 3) := {1, 2}
  have h32 : inner ℝ u₃ u₂ = 0 := by rw [real_inner_comm]; exact h23
  have hon : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict, v, h₂, h₃, h23, h32]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 1 (by simp [s]), hb 2 (by simp [s])⟩

/-- A unit vector orthogonal to a given unit vector. -/
theorem exists_orth_unit {u : Space} (hu : ‖u‖ = 1) :
    ∃ v : Space, ‖v‖ = 1 ∧ inner ℝ v u = 0 := by
  let v : Fin 3 → Space := ![0, 0, u]
  let s : Set (Fin 3) := {2}
  have hon : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [s, Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, v, hu]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb2 : b 2 = u := hb 2 (by simp [s])
  refine ⟨b 0, b.orthonormal.1 0, ?_⟩
  rw [← hb2]
  exact b.orthonormal.2 (by decide)

theorem perp_combo {w u : Space} (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0) (t c : ℝ) :
    perp w (t • w + c • u) = c • u := by
  have hwu : inner ℝ w u = 0 := by rw [real_inner_comm]; exact huw
  simp only [perp, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hw, hwu]
  module

/-- The translate of a parallelepiped has volume `|det|` computed in any orthonormal frame. -/
theorem volume_translate_parallelepiped (b : OrthonormalBasis (Fin 3) ℝ Space) (p : Space)
    (v : Fin 3 → Space) :
    volume ((fun x => p + x) '' parallelepiped v) = ENNReal.ofReal |b.toBasis.det v| := by
  rw [Set.image_add_left, measure_preimage_add, ← b.addHaar_eq_volume,
    Measure.addHaar_parallelepiped]

theorem det_frame (b : OrthonormalBasis (Fin 3) ℝ Space) (v : Fin 3 → Space) :
    b.toBasis.det v = Matrix.det (Matrix.of fun i j => inner ℝ (b i) (v j)) := by
  rw [Module.Basis.det_apply]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply]
  rfl

/-- **Box approximation.** A convex subset of `ball 0 R` containing a unit `ρ`-tube lies in a box
`box a b (2R) z e` with `ρ ≤ a ≤ b ≤ 4R` and `a b ≤ 432 vol W`. -/
theorem box_approx {R ρ : ℝ} (hρ : 0 < ρ) {y w : Space} (hw : ‖w‖ = 1) {W : Set Space}
    (hWc : Convex ℝ W) (hWb : W ⊆ ball 0 R)
    (hT : thickening ρ (segment ℝ y (y + w)) ⊆ W) :
    ∃ (a b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space), ρ ≤ a ∧ a ≤ b ∧ b ≤ 4 * R ∧
      W ⊆ box a b (2 * R) z e ∧ ENNReal.ofReal (a * b) ≤ 432 * volume W := by
  have hc : y + (1 / 2 : ℝ) • w ∈ segment ℝ y (y + w) := by
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp⟩
  have hball : ∀ x, dist x (y + (1 / 2 : ℝ) • w) < ρ → x ∈ W := fun x hx =>
    hT (mem_thickening_iff.mpr ⟨_, hc, hx⟩)
  have hyW : y ∈ W := hT (self_subset_thickening hρ _ (left_mem_segment ℝ y (y + w)))
  have hqW : y + w ∈ W := hT (self_subset_thickening hρ _ (right_mem_segment ℝ y (y + w)))
  have hnorm : ∀ x ∈ W, ‖x‖ < R := fun x hx => by simpa using hWb hx
  have hdist : ∀ x ∈ W, ‖x - y‖ ≤ 2 * R := fun x hx => by
    have := norm_sub_le x y
    linarith [hnorm x hx, hnorm y hyW]
  -- the witness points near the centre of the tube
  have hwit : ∀ u : Space, ‖u‖ = 1 → y + (1 / 2 : ℝ) • w + (ρ / 2) • u ∈ W := fun u hu =>
    hball _ (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith)
  have hwit_sub : ∀ u : Space, y + (1 / 2 : ℝ) • w + (ρ / 2) • u - y =
      (1 / 2 : ℝ) • w + (ρ / 2) • u := fun u => by abel
  -- step 1: the farthest point from the line `y + ℝ w`
  obtain ⟨u, hu, huw⟩ := exists_orth_unit hw
  obtain ⟨M₂, hM₂lo, hM₂hi, hM₂le, r, hrW, hr⟩ :=
    exists_half_max (W := W) (fun x => ‖perp w (x - y)‖) (c := ρ / 2) (B := 2 * R)
      (by positivity) (fun x hx => (norm_perp_le hw _).trans (hdist x hx))
      ⟨_, hwit u hu, by
        rw [hwit_sub, perp_combo hw huw, norm_smul, hu, mul_one, Real.norm_eq_abs,
          abs_of_pos (by positivity)]⟩
  set P := perp w (r - y) with hP
  have hPpos : 0 < ‖P‖ := by linarith
  set u₂ : Space := ‖P‖⁻¹ • P with hu₂
  have hu₂n : ‖u₂‖ = 1 := by
    rw [hu₂, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hPpos.ne']
  have hPw : inner ℝ P w = 0 := by rw [real_inner_comm]; exact inner_perp hw _
  have hu₂w : inner ℝ u₂ w = 0 := by rw [hu₂, inner_smul_left, hPw, mul_zero]
  obtain ⟨fr, hfr1, hfr2⟩ := exists_frame hu₂n hw hu₂w
  set u₁ := fr 0 with hu₁
  have hu₁n : ‖u₁‖ = 1 := fr.orthonormal.1 0
  have hu₁w : inner ℝ u₁ w = 0 := by rw [hu₁, ← hfr2]; exact fr.orthonormal.2 (by decide)
  have hu₁u₂ : inner ℝ u₁ u₂ = 0 := by rw [hu₁, ← hfr1]; exact fr.orthonormal.2 (by decide)
  -- step 2: the farthest point from the plane spanned by `w` and `u₂`
  obtain ⟨M₁, hM₁lo, hM₁hi, hM₁le, s, hsW, hs⟩ :=
    exists_half_max (W := W) (fun x => |inner ℝ u₁ (x - y)|) (c := ρ / 2) (B := M₂)
      (by positivity)
      (fun x hx => (abs_inner_le_norm_perp hu₁n hu₁w _).trans (hM₂le x hx))
      ⟨_, hwit u₁ hu₁n, by
        rw [hwit_sub, inner_add_right, inner_smul_right, inner_smul_right, hu₁w,
          real_inner_self_eq_norm_sq, hu₁n]
        norm_num
        rw [abs_of_pos (by positivity)]⟩
  refine ⟨2 * M₁, 2 * M₂, y - inner ℝ w y • w, fr.repr, by linarith, by linarith, by linarith,
    ?_, ?_⟩
  · -- the box contains `W`
    intro x hx
    have hxz : x - (y - inner ℝ w y • w) = (x - y) + inner ℝ w y • w := by abel
    have hc0 : fr.repr (x - (y - inner ℝ w y • w)) 0 = inner ℝ u₁ (x - y) := by
      rw [OrthonormalBasis.repr_apply_apply, hxz, ← hu₁, inner_add_right, inner_smul_right,
        hu₁w, mul_zero, add_zero]
    have hc1 : fr.repr (x - (y - inner ℝ w y • w)) 1 = inner ℝ u₂ (x - y) := by
      rw [OrthonormalBasis.repr_apply_apply, hxz, hfr1, inner_add_right, inner_smul_right,
        hu₂w, mul_zero, add_zero]
    have hc2 : fr.repr (x - (y - inner ℝ w y • w)) 2 = inner ℝ w x := by
      rw [OrthonormalBasis.repr_apply_apply, hxz, hfr2, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hw, inner_sub_right]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hc0]; linarith [hM₁le x hx]
    · rw [hc1]
      have := (abs_inner_le_norm_perp hu₂n hu₂w (x - y)).trans (hM₂le x hx)
      linarith
    · rw [hc2]
      have := abs_real_inner_le_norm w x
      rw [hw, one_mul] at this
      linarith [hnorm x hx]
  · -- the volume lower bound from the parallelepiped
    let v : Fin 3 → Space := ![(1 / 3 : ℝ) • w, (1 / 3 : ℝ) • (r - y), (1 / 3 : ℝ) • (s - y)]
    have hsub : (fun x => y + x) '' parallelepiped v ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff v x).mp hx
      have ht0 := ht.1
      have ht1 := ht.2
      have h0 : 0 ≤ t 0 := ht0 0
      have h1 : 0 ≤ t 1 := ht0 1
      have h2 : 0 ≤ t 2 := ht0 2
      have h0' : t 0 ≤ 1 := ht1 0
      have h1' : t 1 ≤ 1 := ht1 1
      have h2' : t 2 ≤ 1 := ht1 2
      let wt : Fin 4 → ℝ := ![1 - (t 0 + t 1 + t 2) / 3, t 0 / 3, t 1 / 3, t 2 / 3]
      let pt : Fin 4 → Space := ![y, y + w, r, s]
      have hmem := hWc.sum_mem (t := Finset.univ) (w := wt) (z := pt)
        (by intro i _; fin_cases i <;> simp [wt] <;> linarith)
        (by simp [wt, Fin.sum_univ_four]; ring)
        (by intro i _; fin_cases i <;> simp [pt, hyW, hqW, hrW, hsW])
      convert hmem using 1
      simp only [Fin.sum_univ_four, Fin.sum_univ_three, wt, pt, v, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      module
    have hdet : fr.toBasis.det v = -((1 / 3 * inner ℝ u₁ (s - y)) * (1 / 3 * ‖P‖) * (1 / 3)) := by
      have hry : inner ℝ u₂ (r - y) = ‖P‖ := by
        have h1 : inner ℝ u₂ (r - y) = inner ℝ u₂ P := by
          rw [hP, inner_perp_of_orth hu₂w]
        rw [h1, hu₂, inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [conj_trivial]
        field_simp
      have hry1 : inner ℝ u₁ (r - y) = 0 := by
        have hdec : r - y = P + inner ℝ w (r - y) • w := by rw [hP]; simp [perp]
        have hPu : P = ‖P‖ • u₂ := by
          rw [hu₂, smul_smul, mul_inv_cancel₀ hPpos.ne', one_smul]
        rw [hdec, inner_add_right, inner_smul_right, hu₁w, hPu, inner_smul_right, hu₁u₂]
        ring
      have hu₂w' : inner ℝ u₂ w = 0 := hu₂w
      rw [det_frame, Matrix.det_fin_three]
      simp only [Matrix.of_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, inner_smul_right, hfr1, hfr2,
        ← hu₁, hu₁w, hu₂w', hry, hry1, real_inner_self_eq_norm_sq, hw]
      ring
    have hvol := volume_translate_parallelepiped fr y v
    rw [hdet, abs_neg] at hvol
    have hlow : 2 * M₁ * (2 * M₂) / 432 ≤
        |1 / 3 * inner ℝ u₁ (s - y) * (1 / 3 * ‖P‖) * (1 / 3)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 3),
        abs_of_pos hPpos]
      have hM₁pos : 0 < M₁ := by linarith
      have hM₂pos : 0 < M₂ := by linarith
      nlinarith [mul_lt_mul'' hs hr (by positivity) (by positivity)]
    calc ENNReal.ofReal (2 * M₁ * (2 * M₂))
        = 432 * ENNReal.ofReal (2 * M₁ * (2 * M₂) / 432) := by
          rw [← ENNReal.ofReal_ofNat 432, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
      _ ≤ 432 * volume ((fun x => y + x) '' parallelepiped v) := by
          rw [hvol]; gcongr
      _ ≤ 432 * volume W := by gcongr

/-- A subset of `ball 0 R` lying in a box also lies in the box with the same frame whose first two
sides are capped at `2R` (re-centring the capped coordinates at `0`). -/
theorem box_cap {a b c R : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {W : Set Space}
    (hW : W ⊆ box a b c z e) (hWb : W ⊆ ball 0 R) :
    ∃ z' : Space, W ⊆ box (min a (2 * R)) (min b (2 * R)) c z' e := by
  set c0 : ℝ := if a ≤ 2 * R then 0 else e z 0 with hc0def
  set c1 : ℝ := if b ≤ 2 * R then 0 else e z 1 with hc1def
  set corr : Space := WithLp.toLp 2 ![c0, c1, 0] with hcorr
  refine ⟨z - e.symm corr, fun x hx => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hW hx
  have hxR : ‖x‖ < R := by simpa using hWb hx
  have hcoord : ∀ i, |e x i| < R := fun i => by
    calc |e x i| ≤ ‖e x‖ := by
          have := PiLp.norm_apply_le (e x) i
          rwa [Real.norm_eq_abs] at this
      _ = ‖x‖ := e.norm_map x
      _ < R := hxR
  have hsub : ∀ i, e (x - (z - e.symm corr)) i = e (x - z) i + corr i := by
    intro i
    have : e (x - (z - e.symm corr)) = e (x - z) + corr := by
      rw [sub_sub_eq_add_sub, map_sub, map_add, map_sub, e.apply_symm_apply]
      abel
    rw [this]
    rfl
  have hxz : ∀ i, e (x - z) i = e x i - e z i := by
    intro i; rw [map_sub]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsub]
    have hcorr0 : corr 0 = c0 := rfl
    rw [hcorr0, hc0def]
    split_ifs with ha
    · rw [min_eq_left ha, add_zero]; exact h0
    · rw [min_eq_right (le_of_not_ge ha), hxz, sub_add_cancel]; linarith [hcoord 0]
  · rw [hsub]
    have hcorr1 : corr 1 = c1 := rfl
    rw [hcorr1, hc1def]
    split_ifs with hb
    · rw [min_eq_left hb, add_zero]; exact h1
    · rw [min_eq_right (le_of_not_ge hb), hxz, sub_add_cancel]; linarith [hcoord 1]
  · rw [hsub]
    have hcorr2 : corr 2 = 0 := rfl
    rw [hcorr2, add_zero]
    exact h2

/-- Box approximation with both short sides at most `2R`. -/
theorem box_approx_cap {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ 2 * R) {y w : Space} (hw : ‖w‖ = 1)
    {W : Set Space} (hWc : Convex ℝ W) (hWb : W ⊆ ball 0 R)
    (hT : thickening ρ (segment ℝ y (y + w)) ⊆ W) :
    ∃ (a b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space), ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 * R ∧
      W ⊆ box a b (2 * R) z e ∧ ENNReal.ofReal (a * b) ≤ 432 * volume W := by
  obtain ⟨a, b, z, e, ha, hab, -, hbox, hvol⟩ := box_approx hρ hw hWc hWb hT
  obtain ⟨z', hz'⟩ := box_cap hbox hWb
  refine ⟨min a (2 * R), min b (2 * R), z', e, le_min ha hρR, min_le_min_right _ hab,
    min_le_right _ _, hz', le_trans (ENNReal.ofReal_le_ofReal ?_) hvol⟩
  have ha0 : 0 ≤ min a (2 * R) := le_trans hρ.le (le_min ha hρR)
  exact mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_trans ha0 (min_le_min_right _ hab))
    (le_trans hρ.le ha)

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
