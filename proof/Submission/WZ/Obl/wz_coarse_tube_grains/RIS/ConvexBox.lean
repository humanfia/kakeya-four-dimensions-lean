-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ConvexBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorBox

/-!
# Every convex body in `ℝ³` is comparable to a box

A substitute for John's ellipsoid, used throughout WZ ("`W` is comparable to an `a × b × c`
prism"): a convex set `W ⊆ ball 0 R` containing a ball `ball p r` lies in a box
`box a b c p e` (`0 < a ≤ b ≤ c`) with `a b c ≤ 1728 vol W`. With `p` the centre of the ball,
take `q ∈ W` almost farthest from `p`, then `r' ∈ W` almost farthest from the line `p + ℝ(q-p)`,
then `s ∈ W` almost farthest from the plane through `p, q, r'`; the box has these three
half-widths and `W` contains the parallelepiped spanned by `(q-p)/3, (r'-p)/3, (s-p)/3` at `p`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

theorem box_approx_general {W : Set Space} (hWc : Convex ℝ W) {p : Space} {r R : ℝ}
    (hr : 0 < r) (hball : ball p r ⊆ W) (hWb : W ⊆ ball 0 R) :
    ∃ (a b c : ℝ) (e : Space ≃ₗᵢ[ℝ] Space), 0 < a ∧ a ≤ b ∧ b ≤ c ∧
      W ⊆ box a b c p e ∧ ENNReal.ofReal (a * b * c) ≤ 1728 * volume W := by
  have hpW : p ∈ W := hball (mem_ball_self hr)
  have hnorm : ∀ x ∈ W, ‖x‖ < R := fun x hx => by simpa using hWb hx
  have hdist : ∀ x ∈ W, ‖x - p‖ ≤ 2 * R := fun x hx => by
    have := norm_sub_le x p
    linarith [hnorm x hx, hnorm p hpW]
  have hwit : ∀ u : Space, ‖u‖ = 1 → p + (r / 2) • u ∈ W := fun u hu =>
    hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith)
  have hwit_sub : ∀ u : Space, p + (r / 2) • u - p = (r / 2) • u := fun u => by abel
  -- step 0: a point almost farthest from `p`
  obtain ⟨u₀, hu₀, -⟩ := exists_orth_unit (u := EuclideanSpace.single 0 1)
    (by simp [EuclideanSpace.norm_single])
  obtain ⟨M₃, hM₃lo, hM₃hi, hM₃le, q, hqW, hq⟩ :=
    exists_half_max (W := W) (fun x => ‖x - p‖) (c := r / 2) (B := 2 * R) (by positivity)
      hdist ⟨_, hwit u₀ hu₀, by
        rw [hwit_sub, norm_smul, hu₀, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]⟩
  have hqp : 0 < ‖q - p‖ := by linarith
  set u₃ : Space := ‖q - p‖⁻¹ • (q - p) with hu₃
  have hu₃n : ‖u₃‖ = 1 := by
    rw [hu₃, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hqp.ne']
  have hqp_eq : q - p = ‖q - p‖ • u₃ := by
    rw [hu₃, smul_smul, mul_inv_cancel₀ hqp.ne', one_smul]
  -- step 1: a point almost farthest from the line `p + ℝ u₃`
  obtain ⟨u, hu, huw⟩ := exists_orth_unit hu₃n
  obtain ⟨M₂, hM₂lo, hM₂hi, hM₂le, r', hr'W, hr'⟩ :=
    exists_half_max (W := W) (fun x => ‖perp u₃ (x - p)‖) (c := r / 2) (B := M₃)
      (by positivity) (fun x hx => (norm_perp_le hu₃n _).trans (hM₃le x hx))
      ⟨_, hwit u hu, by
        rw [hwit_sub, show (r / 2) • u = (0 : ℝ) • u₃ + (r / 2) • u by simp,
          perp_combo hu₃n huw, norm_smul, hu, mul_one, Real.norm_eq_abs,
          abs_of_pos (by positivity)]⟩
  set P := perp u₃ (r' - p) with hP
  have hPpos : 0 < ‖P‖ := by linarith
  set u₂ : Space := ‖P‖⁻¹ • P with hu₂
  have hu₂n : ‖u₂‖ = 1 := by
    rw [hu₂, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hPpos.ne']
  have hPw : inner ℝ P u₃ = 0 := by rw [real_inner_comm]; exact inner_perp hu₃n _
  have hu₂w : inner ℝ u₂ u₃ = 0 := by rw [hu₂, inner_smul_left, hPw, mul_zero]
  obtain ⟨fr, hfr1, hfr2⟩ := exists_frame hu₂n hu₃n hu₂w
  set u₁ := fr 0 with hu₁
  have hu₁n : ‖u₁‖ = 1 := fr.orthonormal.1 0
  have hu₁w : inner ℝ u₁ u₃ = 0 := by rw [hu₁, ← hfr2]; exact fr.orthonormal.2 (by decide)
  have hu₁u₂ : inner ℝ u₁ u₂ = 0 := by rw [hu₁, ← hfr1]; exact fr.orthonormal.2 (by decide)
  -- step 2: a point almost farthest from the plane spanned by `u₂, u₃`
  obtain ⟨M₁, hM₁lo, hM₁hi, hM₁le, s, hsW, hs⟩ :=
    exists_half_max (W := W) (fun x => |inner ℝ u₁ (x - p)|) (c := r / 2) (B := M₂)
      (by positivity)
      (fun x hx => (abs_inner_le_norm_perp hu₁n hu₁w _).trans (hM₂le x hx))
      ⟨_, hwit u₁ hu₁n, by
        rw [hwit_sub, inner_smul_right, real_inner_self_eq_norm_sq, hu₁n]
        norm_num
        rw [abs_of_pos (by positivity)]⟩
  refine ⟨2 * M₁, 2 * M₂, 2 * M₃, fr.repr, by linarith, by linarith, by linarith, ?_, ?_⟩
  · -- the box contains `W`
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · rw [OrthonormalBasis.repr_apply_apply, ← hu₁]; linarith [hM₁le x hx]
    · rw [OrthonormalBasis.repr_apply_apply, hfr1]
      have := (abs_inner_le_norm_perp hu₂n hu₂w (x - p)).trans (hM₂le x hx)
      linarith
    · rw [OrthonormalBasis.repr_apply_apply, hfr2]
      have h1 := abs_real_inner_le_norm u₃ (x - p)
      rw [hu₃n, one_mul] at h1
      linarith [hM₃le x hx]
  · -- the volume lower bound from the parallelepiped
    let v : Fin 3 → Space := ![(1 / 3 : ℝ) • (q - p), (1 / 3 : ℝ) • (r' - p), (1 / 3 : ℝ) • (s - p)]
    have hsub : (fun x => p + x) '' parallelepiped v ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff v x).mp hx
      have h0 : 0 ≤ t 0 := ht.1 0
      have h1 : 0 ≤ t 1 := ht.1 1
      have h2 : 0 ≤ t 2 := ht.1 2
      have h0' : t 0 ≤ 1 := ht.2 0
      have h1' : t 1 ≤ 1 := ht.2 1
      have h2' : t 2 ≤ 1 := ht.2 2
      let wt : Fin 4 → ℝ := ![1 - (t 0 + t 1 + t 2) / 3, t 0 / 3, t 1 / 3, t 2 / 3]
      let pt : Fin 4 → Space := ![p, q, r', s]
      have hmem := hWc.sum_mem (t := Finset.univ) (w := wt) (z := pt)
        (by intro i _; fin_cases i <;> simp [wt] <;> linarith)
        (by simp [wt, Fin.sum_univ_four]; ring)
        (by intro i _; fin_cases i <;> simp [pt, hpW, hqW, hr'W, hsW])
      convert hmem using 1
      simp only [Fin.sum_univ_four, Fin.sum_univ_three, wt, pt, v, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      module
    have hdet : fr.toBasis.det v =
        -((1 / 3 * inner ℝ u₁ (s - p)) * (1 / 3 * ‖P‖) * (1 / 3 * ‖q - p‖)) := by
      have hry : inner ℝ u₂ (r' - p) = ‖P‖ := by
        have h1 : inner ℝ u₂ (r' - p) = inner ℝ u₂ P := by
          rw [hP, inner_perp_of_orth hu₂w]
        rw [h1, hu₂, inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [conj_trivial]
        field_simp
      have hry1 : inner ℝ u₁ (r' - p) = 0 := by
        have hdec : r' - p = P + inner ℝ u₃ (r' - p) • u₃ := by rw [hP]; simp [perp]
        have hPu : P = ‖P‖ • u₂ := by
          rw [hu₂, smul_smul, mul_inv_cancel₀ hPpos.ne', one_smul]
        rw [hdec, inner_add_right, inner_smul_right, hu₁w, hPu, inner_smul_right, hu₁u₂]
        ring
      have hq0 : inner ℝ u₁ (q - p) = 0 := by
        rw [hqp_eq, inner_smul_right, hu₁w, mul_zero]
      have hq1 : inner ℝ u₂ (q - p) = 0 := by
        rw [hqp_eq, inner_smul_right, hu₂w, mul_zero]
      have hq2 : inner ℝ u₃ (q - p) = ‖q - p‖ := by
        conv_lhs => rw [hqp_eq]
        rw [inner_smul_right, real_inner_self_eq_norm_sq, hu₃n]
        ring
      rw [det_frame, Matrix.det_fin_three]
      simp only [Matrix.of_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, inner_smul_right, hfr1, hfr2,
        ← hu₁, hq0, hq1, hq2, hry, hry1]
      ring
    have hvol := volume_translate_parallelepiped fr p v
    rw [hdet, abs_neg] at hvol
    have hlow : 2 * M₁ * (2 * M₂) * (2 * M₃) / 1728 ≤
        |1 / 3 * inner ℝ u₁ (s - p) * (1 / 3 * ‖P‖) * (1 / 3 * ‖q - p‖)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 3),
        abs_of_pos hPpos, abs_of_pos hqp]
      have hM₁pos : 0 < M₁ := by linarith
      have hM₂pos : 0 < M₂ := by linarith
      have hM₃pos : 0 < M₃ := by linarith
      have h12 := mul_lt_mul'' hs hr' (by positivity) (by positivity)
      have h123 := mul_lt_mul'' h12 hq (by positivity) (by positivity)
      nlinarith
    calc ENNReal.ofReal (2 * M₁ * (2 * M₂) * (2 * M₃))
        = 1728 * ENNReal.ofReal (2 * M₁ * (2 * M₂) * (2 * M₃) / 1728) := by
          rw [← ENNReal.ofReal_ofNat 1728, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
      _ ≤ 1728 * volume ((fun x => p + x) '' parallelepiped v) := by
          rw [hvol]; gcongr
      _ ≤ 1728 * volume W := by gcongr

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
