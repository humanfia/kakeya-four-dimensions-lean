-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NearHorizontal
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Nondegenerate
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Rescale
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Extremal
import Submission.WZ.Obl.wz_tube_packing_bound

/-!
# Assembly: normalized nonsingular examples

Choose the error and scale parameters (`main_params`: every requirement is a fixed positive
power of `δ` beating a constant, possibly with a logarithmic loss), extract a grains example,
and discard the points on sparse grains (extremality, `main_sparse`), the nearly horizontal
tubes (`near_horizontal_mass`) and the end strips (`main_end`). Pigeonholing over thin slabs of
width `b = L / 1000` (`main_mass`) gives a slab carrying a fair share of the good mass; the
nondegeneracy lemma on a window of length `L` around it shows `|f'| > L` there (`main_slope`),
so `|f'|` is comparable to `m` on the thin slab (`main_subslab`). Many transversal tubes have
dense shading in the slab (`main_count`), and `rescale` produces the normalized family.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- A power with a logarithmic loss is eventually below one. -/
private lemma main_cut_one {C e : ℝ} (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * (1 + Real.log (1 / δ)) * δ ^ e ≤ 1 := by
  obtain ⟨d, hd, hcut⟩ := exists_rpow_cutoff (half_pos he)
    (show 0 < 1 / ((|C| + 1) * (1 + 2 / e)) by positivity)
  refine ⟨min d 1, lt_min hd one_pos, fun δ hδ hδd => ?_⟩
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  have h1 := hcut δ hδ (hδd.trans (min_le_left _ _))
  have hlog0 : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hlog : Real.log (1 / δ) ≤ (1 / δ) ^ (e / 2) / (e / 2) :=
    Real.log_le_rpow_div (by positivity) (half_pos he)
  have hinv : (1 / δ) ^ (e / 2) * δ ^ e = δ ^ (e / 2) := by
    rw [one_div, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le, ← Real.rpow_add hδ]
    ring_nf
  have hle : δ ^ e ≤ δ ^ (e / 2) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hkey : (1 + Real.log (1 / δ)) * δ ^ e ≤ (1 + 2 / e) * δ ^ (e / 2) := by
    have h2 : Real.log (1 / δ) * δ ^ e ≤ (2 / e) * δ ^ (e / 2) := by
      calc Real.log (1 / δ) * δ ^ e ≤ ((1 / δ) ^ (e / 2) / (e / 2)) * δ ^ e :=
            mul_le_mul_of_nonneg_right hlog (by positivity)
        _ = (2 / e) * ((1 / δ) ^ (e / 2) * δ ^ e) := by field_simp
        _ = (2 / e) * δ ^ (e / 2) := by rw [hinv]
    nlinarith
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * (1 + Real.log (1 / δ)) * δ ^ e = C * ((1 + Real.log (1 / δ)) * δ ^ e) := by ring
    _ ≤ (|C| + 1) * ((1 + Real.log (1 / δ)) * δ ^ e) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ (|C| + 1) * ((1 + 2 / e) * δ ^ (e / 2)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ (|C| + 1) * ((1 + 2 / e) * (1 / ((|C| + 1) * (1 + 2 / e)))) := by gcongr
    _ = 1 := by field_simp

/-- Comparison of two powers with a logarithmic loss, for small `δ`. -/
private lemma main_cut {A B e1 e2 : ℝ} (hB : 0 < B) (he : e2 < e1) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      A * (1 + Real.log (1 / δ)) * δ ^ e1 ≤ B * δ ^ e2 := by
  obtain ⟨d, hd, h⟩ := main_cut_one (C := A / B) (sub_pos.mpr he)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have h1 := h δ hδ hδd
  have hpos : 0 < B * δ ^ e2 := by positivity
  have hsplit : δ ^ e1 = δ ^ (e1 - e2) * δ ^ e2 := by
    rw [← Real.rpow_add hδ]; ring_nf
  calc A * (1 + Real.log (1 / δ)) * δ ^ e1
      = (A / B * (1 + Real.log (1 / δ)) * δ ^ (e1 - e2)) * (B * δ ^ e2) := by
        rw [hsplit]; field_simp
    _ ≤ 1 * (B * δ ^ e2) := mul_le_mul_of_nonneg_right h1 hpos.le
    _ = B * δ ^ e2 := one_mul _

/-- Comparison of two powers, for small `δ`. -/
private lemma main_cut' {A B e1 e2 : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (he : e2 < e1) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → A * δ ^ e1 ≤ B * δ ^ e2 := by
  obtain ⟨d, hd, h⟩ := main_cut (A := A) hB he
  refine ⟨min d 1, lt_min hd one_pos, fun δ hδ hδd => ?_⟩
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  have h1 := h δ hδ (hδd.trans (min_le_left _ _))
  have hlog0 : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  calc A * δ ^ e1 ≤ A * (1 + Real.log (1 / δ)) * δ ^ e1 := by
        have : A ≤ A * (1 + Real.log (1 / δ)) := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ ≤ B * δ ^ e2 := h1

/-- Two properties of small `δ` hold simultaneously for small `δ`. -/
private lemma main_and {P Q : ℝ → Prop}
    (hP : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → P δ)
    (hQ : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → Q δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → P δ ∧ Q δ := by
  obtain ⟨d1, hd1, h1⟩ := hP
  obtain ⟨d2, hd2, h2⟩ := hQ
  exact ⟨min d1 d2, lt_min hd1 hd2, fun δ hδ hδd =>
    ⟨h1 δ hδ (hδd.trans (min_le_left _ _)), h2 δ hδ (hδd.trans (min_le_right _ _))⟩⟩

/-- A property of small `δ ≤ 1` implies another one. -/
private lemma main_mono {P Q : ℝ → Prop}
    (hP : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → P δ)
    (hPQ : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → P δ → Q δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → Q δ := by
  obtain ⟨d, hd, h⟩ := hP
  exact ⟨min d 1, lt_min hd one_pos, fun δ hδ hδd =>
    hPQ δ hδ (hδd.trans (min_le_right _ _)) (h δ hδ (hδd.trans (min_le_left _ _)))⟩

/-- All parameter requirements hold for small `δ`. -/
private lemma main_params {σ η1 ε2 c εe η η0 de d0 KNH KND KR Cp : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hη1 : 0 < η1) (hη1' : η1 ≤ 1 / 100)
    (hε2 : ε2 = η1 / 100) (hc : c = σ ^ 2 * ε2 / 100) (hεe : εe = c / 10)
    (hη : 0 < η) (hηη0 : η ≤ η0 / 2) (hηc : η ≤ σ * c / 200)
    (hde : 0 < de) (hd0 : 0 < d0) (hKND : 0 ≤ KND) (hCp : 0 ≤ Cp) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      4 * δ / δ ^ c ≤ d0 ∧
      4 * δ / δ ^ c ≤ 1 / 100 ∧
      δ ≤ de ∧
      δ ^ η0 ≤ δ ^ η / 8 ∧
      KNH * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4) ≤ δ ^ η / 8 ∧
      δ ^ c ≤ 1 / 100 ∧
      3456 * (δ ^ ε2 / 1000) / δ ^ c ≤ δ ^ η / 8 ∧
      100 * δ ≤ δ ^ ε2 ∧
      10 * δ ^ ε2 ≤ δ ^ c ∧
      KND * δ ^ (σ / 2) ≤ δ ^ (εe + η) / 32 * δ ^ η ∧
      KND ^ (2 / σ) * (δ ^ ε2) ^ σ ≤
        (δ ^ (εe + η) / 32 * (δ ^ η / 5000) * δ ^ c * δ ^ η) ^ (7 / σ) ∧
      400 * δ ≤ δ ^ c ∧
      100 * δ ≤ δ ^ ε2 / 1000 ∧
      KR * (1 + Real.log (1 / δ)) * (4 * δ / δ ^ c) ^ η1 ≤
        (δ ^ η / 40 * (δ ^ (η + c) / 5000) * (δ ^ ε2 / 1000) * δ ^ c * δ ^ η) ^ 4 ∧
      Cp * δ ≤ 1 ∧
      8 * δ ^ (σ - η) ≤ δ ^ (σ / 8) / 2 := by
  -- exponent facts
  have hε2p : 0 < ε2 := by rw [hε2]; positivity
  have hε2s : ε2 ≤ 1 / 10000 := by rw [hε2]; linarith
  have hσ2 : σ ^ 2 ≤ σ := pow_le_of_le_one hσ.le hσ1.le two_ne_zero
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcσ : c ≤ σ * (ε2 / 100) := by
    rw [hc]
    calc σ ^ 2 * ε2 / 100 = σ ^ 2 * (ε2 / 100) := by ring
      _ ≤ σ * (ε2 / 100) := mul_le_mul_of_nonneg_right hσ2 (by positivity)
  have hcε : c ≤ ε2 / 100 := hcσ.trans (mul_le_of_le_one_left (by positivity) hσ1.le)
  have hc1 : c < 1 := by linarith
  have hσc : σ * c ≤ c := mul_le_of_le_one_left hc0.le hσ1.le
  have hσc0 : 0 < σ * c := mul_pos hσ hc0
  have hηc' : η ≤ c / 200 := by linarith
  have hεe0 : 0 < εe := by rw [hεe]; positivity
  have h100c : ε2 * σ * σ = 100 * c := by rw [hc]; ring
  have hσε : σ * (ε2 / 100) ≤ σ * (1 / 1000000) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ.le
  -- each condition
  have P1 : ∀ D : ℝ, 0 < D → ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → 4 * δ / δ ^ c ≤ D := by
    intro D hD
    refine main_mono (main_cut' (A := 4) (B := D) (e1 := 1 - c) (e2 := 0) (by norm_num) hD
      (by linarith)) (fun δ hδ _ h => ?_)
    rw [Real.rpow_zero, mul_one, Real.rpow_sub hδ, Real.rpow_one] at h
    rw [mul_div_assoc]; exact h
  refine main_and (P1 d0 hd0) (main_and (P1 (1 / 100) (by norm_num)) (main_and
    ⟨de, hde, fun δ _ h => h⟩ (main_and ?_ (main_and ?_ (main_and ?_ (main_and ?_
    (main_and ?_ (main_and ?_ (main_and ?_ (main_and ?_ (main_and ?_ (main_and ?_
    (main_and ?_ (main_and ?_ ?_))))))))))))))
  · -- δ ^ η0 ≤ δ ^ η / 8
    refine main_mono (main_cut' (A := 1) (B := 1 / 8) (e1 := η0) (e2 := η) (by norm_num)
      (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    linarith
  · -- near horizontal
    refine main_mono (main_cut (A := KNH) (B := 1 / 8) (e1 := σ * c / 4 - 2 * η) (e2 := η)
      (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    have he : δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4) = δ ^ (σ * c / 4 - 2 * η) := by
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
    calc KNH * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4)
        = KNH * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4)) := by ring
      _ = KNH * (1 + Real.log (1 / δ)) * δ ^ (σ * c / 4 - 2 * η) := by rw [he]
      _ ≤ 1 / 8 * δ ^ η := h
      _ = δ ^ η / 8 := by ring
  · -- θ ≤ 1/100
    refine main_mono (main_cut' (A := 1) (B := 1 / 100) (e1 := c) (e2 := 0) (by norm_num)
      (by norm_num) hc0) (fun δ hδ _ h => ?_)
    simpa using h
  · -- end strips
    refine main_mono (main_cut' (A := 3456 / 1000) (B := 1 / 8) (e1 := ε2 - c) (e2 := η)
      (by norm_num) (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    rw [Real.rpow_sub hδ] at h
    calc 3456 * (δ ^ ε2 / 1000) / δ ^ c = 3456 / 1000 * (δ ^ ε2 / δ ^ c) := by ring
      _ ≤ 1 / 8 * δ ^ η := h
      _ = δ ^ η / 8 := by ring
  · -- 100 δ ≤ L
    refine main_mono (main_cut' (A := 100) (B := 1) (e1 := 1) (e2 := ε2) (by norm_num)
      (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    simpa using h
  · -- 10 L ≤ θ
    refine main_mono (main_cut' (A := 10) (B := 1) (e1 := ε2) (e2 := c) (by norm_num)
      (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    simpa using h
  · -- nondegenerate, first
    refine main_mono (main_cut' (A := KND) (B := 1 / 32) (e1 := σ / 2) (e2 := εe + 2 * η)
      hKND (by norm_num) (by rw [hεe]; linarith)) (fun δ hδ _ h => ?_)
    have he : δ ^ (εe + η) / 32 * δ ^ η = 1 / 32 * δ ^ (εe + 2 * η) := by
      rw [show εe + 2 * η = (εe + η) + η by ring, Real.rpow_add hδ (εe + η) η]; ring
    rw [he]; exact h
  · -- nondegenerate, second
    refine main_mono (main_cut' (A := KND ^ (2 / σ)) (B := (1 / 160000) ^ (7 / σ))
      (e1 := ε2 * σ) (e2 := (εe + 3 * η + c) * (7 / σ)) (by positivity) (by positivity)
      ?_) (fun δ hδ _ h => ?_)
    · rw [show (εe + 3 * η + c) * (7 / σ) = 7 * (εe + 3 * η + c) / σ by ring,
        div_lt_iff₀ hσ, hεe, h100c]
      linarith
    · have h1 : (δ ^ ε2) ^ σ = δ ^ (ε2 * σ) := by rw [← Real.rpow_mul hδ.le]
      have h2 : δ ^ (εe + η) / 32 * (δ ^ η / 5000) * δ ^ c * δ ^ η =
          1 / 160000 * δ ^ (εe + 3 * η + c) := by
        have : δ ^ (εe + 3 * η + c) = δ ^ (εe + η) * δ ^ η * δ ^ c * δ ^ η := by
          rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
        rw [this]; ring
      rw [h1, h2, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le]
      exact h
  · -- 400 δ ≤ θ
    refine main_mono (main_cut' (A := 400) (B := 1) (e1 := 1) (e2 := c) (by norm_num)
      (by norm_num) hc1) (fun δ hδ _ h => ?_)
    simpa using h
  · -- 100 δ ≤ b
    refine main_mono (main_cut' (A := 100000) (B := 1) (e1 := 1) (e2 := ε2) (by norm_num)
      (by norm_num) (by linarith)) (fun δ hδ _ h => ?_)
    simp only [Real.rpow_one, one_mul] at h
    linarith
  · -- rescale
    refine main_mono (main_cut (A := KR * 4 ^ η1) (B := (1 / 200000000) ^ 4)
      (e1 := (1 - c) * η1) (e2 := 4 * (3 * η + 2 * c + ε2)) (by positivity) ?_)
      (fun δ hδ _ h => ?_)
    · have hcs : c * η1 ≤ 1 / 1000000 * η1 := mul_le_mul_of_nonneg_right (by linarith) hη1.le
      have hη1e : η1 = 100 * ε2 := by rw [hε2]; ring
      rw [sub_mul, one_mul]
      linarith
    · have h1 : (4 * δ / δ ^ c) ^ η1 = 4 ^ η1 * δ ^ ((1 - c) * η1) := by
        have : δ / δ ^ c = δ ^ (1 - c) := by rw [Real.rpow_sub hδ, Real.rpow_one]
        rw [mul_div_assoc, this, Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_mul hδ.le]
      have h2 : δ ^ η / 40 * (δ ^ (η + c) / 5000) * (δ ^ ε2 / 1000) * δ ^ c * δ ^ η =
          1 / 200000000 * δ ^ (3 * η + 2 * c + ε2) := by
        have : δ ^ (3 * η + 2 * c + ε2) = δ ^ η * δ ^ (η + c) * δ ^ ε2 * δ ^ c * δ ^ η := by
          rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
          congr 1; ring
        rw [this]; ring
      have h3 : (δ ^ (3 * η + 2 * c + ε2)) ^ 4 = δ ^ (4 * (3 * η + 2 * c + ε2)) := by
        rw [← Real.rpow_mul_natCast hδ.le]; congr 1; push_cast; ring
      rw [h1, h2, mul_pow, h3]
      calc KR * (1 + Real.log (1 / δ)) * (4 ^ η1 * δ ^ ((1 - c) * η1))
          = KR * 4 ^ η1 * (1 + Real.log (1 / δ)) * δ ^ ((1 - c) * η1) := by ring
        _ ≤ _ := h
  · -- packing
    refine main_mono (main_cut' (A := Cp) (B := 1) (e1 := 1) (e2 := 0) hCp
      (by norm_num) (by norm_num)) (fun δ hδ _ h => ?_)
    simpa using h
  · -- slices
    obtain ⟨d, hd, h⟩ := exists_slice_cutoff (σ := σ) (η := η) (by linarith)
    exact ⟨d, hd, h⟩

/-- A derivative bound on a convex set gives a Lipschitz bound there. -/
private lemma main_lip_of_deriv {g : ℝ → ℝ} {s : Set ℝ} {C : ℝ} (hs : Convex ℝ s)
    (hg : Differentiable ℝ g) (hb : ∀ t ∈ s, |deriv g t| ≤ C) :
    ∀ z ∈ s, ∀ z' ∈ s, |g z - g z'| ≤ C * |z - z'| := by
  intro z hz z' hz'
  have h := hs.norm_image_sub_le_of_norm_deriv_le (fun t _ => hg t)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ht) hz' hz
  simpa only [Real.norm_eq_abs] using h

/-- The derivative of a `C²` function is differentiable. -/
private lemma main_diff_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (deriv f) := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  have h : ContDiff ℝ (1 + 1) f := h2 ▸ hf
  exact ((contDiff_succ_iff_deriv.mp h).2.2).differentiable (by norm_num)

/-- Inner product with the third basis vector. -/
private lemma main_inner_e2 (p : Space) :
    inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p = p 2 := by
  simp [EuclideanSpace.inner_single_left]

/-- A transversal tube meets a horizontal slab in small volume. -/
private lemma main_slab_le {δ r θ c : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hθ : 0 < θ)
    {x v : Space} (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|) :
    volume (Tube δ x v ∩ {p : Space | |p 2 - c| ≤ r}) ≤
      ENNReal.ofReal (1152 * r * δ ^ 2 / θ) := by
  have hu : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ 1 := by simp
  have hq : 0 < |inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) v| := by
    rw [main_inner_e2]; linarith
  have h := tube_slab_volume_le hδ hδr x v _ hv hu hq c
  simp only [main_inner_e2] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv2 : 0 < |v 2| := hθ.trans_le hθv
  have hr : 0 < r := hδ.trans_le hδr
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have : |v 2|⁻¹ ≤ θ⁻¹ := inv_anti₀ hθ hθv
  have h2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  calc 1152 * (r * |v 2|⁻¹) * δ ^ 2 = 1152 * r * δ ^ 2 * |v 2|⁻¹ := by ring
    _ ≤ 1152 * r * δ ^ 2 * θ⁻¹ := by gcongr

/-- The points of `E` on grains with fibres shorter than `lam`. -/
private def main_sp (f : ℝ → ℝ) (E : Set Space) (lam : ℝ) : Set Space :=
  {q | q ∈ E ∧ volume (grainFib f E (twist f q) (q 2)) < ENNReal.ofReal lam}

/-- The good part of a shading: empty for nearly horizontal tubes, and with the sparse points
removed otherwise. -/
private noncomputable def main_good (θ : ℝ) (v : Space) (Y Sp : Set Space) : Set Space :=
  if θ ≤ |v 2| then Y \ Sp else ∅

private lemma main_good_sub {θ : ℝ} {v : Space} {Y Sp : Set Space} :
    main_good θ v Y Sp ⊆ Y := by
  unfold main_good; split_ifs
  · exact sdiff_subset
  · exact empty_subset _

private lemma main_good_empty {θ : ℝ} {v : Space} {Y Sp : Set Space} (h : ¬ θ ≤ |v 2|) :
    main_good θ v Y Sp = ∅ := by
  unfold main_good; rw [ite_eq_right h]

private lemma main_good_meas {θ : ℝ} {v : Space} {Y Sp : Set Space} (hY : MeasurableSet Y)
    (hSp : MeasurableSet Sp) : MeasurableSet (main_good θ v Y Sp) := by
  unfold main_good; split_ifs
  · exact hY.diff hSp
  · exact MeasurableSet.empty

private lemma main_good_full {f : ℝ → ℝ} {n : ℕ} {Y : Fin n → Set Space} {lam θ : ℝ}
    {v : Space} (i : Fin n) :
    main_good θ v (Y i) (main_sp f (⋃ j, Y j) lam) ⊆ FullPart f (⋃ j, Y j) lam := by
  intro q hq
  unfold main_good at hq
  split_ifs at hq with h
  · obtain ⟨hqY, hqS⟩ := hq
    simp only [main_sp, mem_ofPred_eq, not_and, not_lt] at hqS
    exact hqS (mem_iUnion.mpr ⟨i, hqY⟩)
  · exact absurd hq (notMem_empty q)

/-- Extremality: the sparse points carry little shading mass. -/
private lemma main_sparse {σ εe η η0 de δ lam s : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} {f : ℝ → ℝ}
    (hlower : ∀ η' δ : ℝ, η' ≤ η0 → 0 < δ → δ ≤ de → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Dense η' δ n x v Y → Strong η' δ n x v →
          ENNReal.ofReal (δ ^ (σ + εe)) < volume (⋃ i, Y i))
    (hδ : 0 < δ) (hδde : δ ≤ de) (hδ100 : δ ≤ 1 / 100) (hηη0 : η ≤ η0)
    (hD : Dense η δ n x v Y) (hS : Strong η δ n x v) (hf : Continuous f)
    (hs0 : 0 ≤ s) (hlam : 0 ≤ lam)
    (hs : ∀ z ∈ Icc (-1 : ℝ) 1, volume (PS f (⋃ i, Y i) z) ≤ ENNReal.ofReal s)
    (hls : 2 * lam * s ≤ δ ^ (σ + εe) / 2) :
    ∑ i, volume (Y i ∩ main_sp f (⋃ i, Y i) lam) < ENNReal.ofReal (δ ^ η0 * n * δ ^ 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn, hv, hball, hsep, hmeas, hsub, _⟩ := hD
  have hE : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hmeas
  have hEb : (⋃ i, Y i) ⊆ ball 0 1 := iUnion_subset fun i => (hsub i).trans (hball i)
  have hSpm : MeasurableSet (main_sp f (⋃ i, Y i) lam) := sparse_measurableSet hf hE lam
  have hSpv : volume (main_sp f (⋃ i, Y i) lam) ≤ ENNReal.ofReal (2 * lam * s) :=
    sparse_volume_le hf hE hEb hs0 hlam hs
  have hD' : Dense η0 δ n x v (fun i => Y i ∩ main_sp f (⋃ i, Y i) lam) :=
    ⟨hn, hv, hball, hsep, fun i => (hmeas i).inter hSpm,
      fun i => inter_subset_left.trans (hsub i), hcon⟩
  have hS' := strong_mono_error hδ (by linarith) hηη0 hS
  have hlt := hlower η0 δ le_rfl hδ hδde hδ100 n x v _ hD' hS'
  have hsub' : (⋃ i, Y i ∩ main_sp f (⋃ i, Y i) lam) ⊆ main_sp f (⋃ i, Y i) lam :=
    iUnion_subset fun i => inter_subset_right
  have h2 := hlt.trans_le ((measure_mono hsub').trans
    (hSpv.trans (ENNReal.ofReal_le_ofReal hls)))
  have hpos : 0 < δ ^ (σ + εe) := Real.rpow_pos_of_pos hδ _
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h2
  linarith

/-- Points of a transversal tube outside the middle slab lie in two thin end slabs. -/
private lemma main_end {δ θ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) (hδb : δ ≤ 3 * b / 2)
    (hθ : 0 < θ) {x v : Space} (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|) (hT : Tube δ x v ⊆ ball 0 1)
    {Y : Set Space} (hY : Y ⊆ Tube δ x v) :
    volume (Y \ {q : Space | -1 + 3 * b ≤ q 2 ∧ q 2 ≤ 1 - 3 * b}) ≤
      ENNReal.ofReal (3456 * b * δ ^ 2 / θ) := by
  have hsub : Y \ {q : Space | -1 + 3 * b ≤ q 2 ∧ q 2 ≤ 1 - 3 * b} ⊆
      (Tube δ x v ∩ {p : Space | |p 2 - (-1 + 3 * b / 2)| ≤ 3 * b / 2}) ∪
      (Tube δ x v ∩ {p : Space | |p 2 - (1 - 3 * b / 2)| ≤ 3 * b / 2}) := by
    rintro q ⟨hqY, hqM⟩
    have hqT := hY hqY
    have hq1 : |q 2| < 1 := (PiLp.norm_apply_le q 2).trans_lt (mem_ball_zero_iff.mp (hT hqT))
    rw [abs_lt] at hq1
    simp only [mem_ofPred_eq, not_and_or, not_le] at hqM
    rcases hqM with h | h
    · left; refine ⟨hqT, ?_⟩; simp only [mem_ofPred_eq]; rw [abs_le]; constructor <;> linarith
    · right; refine ⟨hqT, ?_⟩; simp only [mem_ofPred_eq]; rw [abs_le]; constructor <;> linarith
  calc volume (Y \ {q : Space | -1 + 3 * b ≤ q 2 ∧ q 2 ≤ 1 - 3 * b})
      ≤ volume ((Tube δ x v ∩ {p : Space | |p 2 - (-1 + 3 * b / 2)| ≤ 3 * b / 2}) ∪
      (Tube δ x v ∩ {p : Space | |p 2 - (1 - 3 * b / 2)| ≤ 3 * b / 2})) := measure_mono hsub
    _ ≤ volume (Tube δ x v ∩ {p : Space | |p 2 - (-1 + 3 * b / 2)| ≤ 3 * b / 2}) +
        volume (Tube δ x v ∩ {p : Space | |p 2 - (1 - 3 * b / 2)| ≤ 3 * b / 2}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (1152 * (3 * b / 2) * δ ^ 2 / θ) +
        ENNReal.ofReal (1152 * (3 * b / 2) * δ ^ 2 / θ) :=
        add_le_add (main_slab_le hδ hδb hθ hv hθv) (main_slab_le hδ hδb hθ hv hθv)
    _ = ENNReal.ofReal (3456 * b * δ ^ 2 / θ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Splitting the shading mass into sparse, nearly horizontal, good central and end parts. -/
private lemma main_decomp {n : ℕ} {v : Fin n → Space} {Y : Fin n → Set Space}
    {Sp M : Set Space} {θ : ℝ} :
    ∑ i, volume (Y i) ≤ ∑ i, volume (Y i ∩ Sp) +
      ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) +
      ∑ i, volume (main_good θ (v i) (Y i) Sp ∩ M) +
      ∑ i ∈ Finset.univ.filter (fun i => θ ≤ |v i 2|), volume (Y i \ M) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : θ ≤ |v i 2|
  · have h' : ¬ |v i 2| < θ := not_lt.mpr h
    simp only [main_good, ite_eq_left h, ite_eq_right h', add_zero]
    calc volume (Y i) ≤ volume ((Y i ∩ Sp) ∪ ((Y i \ Sp) ∩ M) ∪ (Y i \ M)) := by
          apply measure_mono
          intro q hq
          by_cases hs : q ∈ Sp
          · exact Or.inl (Or.inl ⟨hq, hs⟩)
          by_cases hm : q ∈ M
          · exact Or.inl (Or.inr ⟨⟨hq, hs⟩, hm⟩)
          exact Or.inr ⟨hq, hm⟩
      _ ≤ volume ((Y i ∩ Sp) ∪ ((Y i \ Sp) ∩ M)) + volume (Y i \ M) := measure_union_le _ _
      _ ≤ volume (Y i ∩ Sp) + volume ((Y i \ Sp) ∩ M) + volume (Y i \ M) := by
          gcongr; exact measure_union_le _ _
  · have h' : |v i 2| < θ := not_le.mp h
    simp only [ite_eq_left h', ite_eq_right h, add_zero]
    calc volume (Y i) ≤ volume (Y i ∩ Sp) + volume (Y i) := le_add_self
      _ ≤ _ := le_self_add

/-- Pigeonhole in `ℝ≥0∞`. -/
private lemma main_pigeon {ι : Type*} {V : Finset ι} (hV : V.Nonempty) {F : ι → ℝ≥0∞}
    {B X : ℝ} (hX : ENNReal.ofReal X ≤ ∑ j ∈ V, F j) (hcard : (V.card : ℝ) * B ≤ X) :
    ∃ j ∈ V, ENNReal.ofReal B ≤ F j := by
  by_contra h
  push Not at h
  have hlt := ENNReal.sum_lt_sum_of_nonempty hV h
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hlt
  exact absurd (hX.trans_lt hlt) (not_lt.mpr (ENNReal.ofReal_le_ofReal hcard))

/-- The thin slabs of width `b` centred at `-1 + (j + 1/2) b`, `2 ≤ j`, `(j + 5/2) b ≤ 2`,
cover the middle region. -/
private lemma main_cover {b t : ℝ} (hb : 0 < b) (ht1 : -1 + 3 * b ≤ t) (ht2 : t ≤ 1 - 3 * b) :
    ∃ j ∈ (Finset.range (⌊2 / b⌋₊ + 1)).filter
      (fun j : ℕ => 2 ≤ j ∧ ((j : ℝ) + 5 / 2) * b ≤ 2),
      |t - (-1 + ((j : ℝ) + 1 / 2) * b)| ≤ b / 2 := by
  have h0 : 0 ≤ (t + 1) / b := div_nonneg (by linarith) hb.le
  have hjle : (⌊(t + 1) / b⌋₊ : ℝ) ≤ (t + 1) / b := Nat.floor_le h0
  have hjlt : (t + 1) / b < ⌊(t + 1) / b⌋₊ + 1 := Nat.lt_floor_add_one _
  have hjle' : (⌊(t + 1) / b⌋₊ : ℝ) * b ≤ t + 1 := by rwa [le_div_iff₀ hb] at hjle
  have hjlt' : t + 1 < ((⌊(t + 1) / b⌋₊ : ℝ) + 1) * b := by rwa [div_lt_iff₀ hb] at hjlt
  refine ⟨⌊(t + 1) / b⌋₊, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have : ⌊(t + 1) / b⌋₊ ≤ ⌊2 / b⌋₊ :=
        Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hb.le)
      omega
    · apply Nat.le_floor
      rw [le_div_iff₀ hb]; push_cast; linarith
    · rw [add_mul]; linarith
  · have e : t - (-1 + ((⌊(t + 1) / b⌋₊ : ℝ) + 1 / 2) * b) =
        (t + 1) - (⌊(t + 1) / b⌋₊ : ℝ) * b - b / 2 := by ring
    have e' : ((⌊(t + 1) / b⌋₊ : ℝ) + 1) * b = (⌊(t + 1) / b⌋₊ : ℝ) * b + b := by ring
    rw [e, abs_le]
    rw [e'] at hjlt'
    constructor <;> linarith

/-- The good shading carries a fair share of the mass in a thin slab of width `b`,
whose centre stays `2b` inside `[-1, 1]`. -/
private lemma main_mass {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space} {Sp : Set Space}
    {δ θ b A : ℝ} (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1 / 10) (hδb : δ ≤ 3 * b / 2)
    (hθ : 0 < θ) (hA : 0 ≤ A)
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hsub : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hmass : ENNReal.ofReal A ≤ ∑ i, volume (Y i))
    (hSp : ∑ i, volume (Y i ∩ Sp) ≤ ENNReal.ofReal (A / 8))
    (hNH : ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) ≤
      ENNReal.ofReal (A / 8))
    (hend : (n : ℝ) * (3456 * b * δ ^ 2 / θ) ≤ A / 8) :
    ∃ a : ℝ, |a| + 2 * b ≤ 1 ∧
      ENNReal.ofReal (5 * A * b / 24) ≤
        ∑ i, volume (main_good θ (v i) (Y i) Sp ∩ {q : Space | |q 2 - a| ≤ b / 2}) := by
  classical
  set M : Set Space := {q : Space | -1 + 3 * b ≤ q 2 ∧ q 2 ≤ 1 - 3 * b} with hM
  have hdec := main_decomp (v := v) (Y := Y) (Sp := Sp) (M := M) (θ := θ)
  -- the end strips
  have hE : ∑ i ∈ Finset.univ.filter (fun i => θ ≤ |v i 2|), volume (Y i \ M) ≤
      ENNReal.ofReal (A / 8) := by
    calc ∑ i ∈ Finset.univ.filter (fun i => θ ≤ |v i 2|), volume (Y i \ M)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => θ ≤ |v i 2|),
            ENNReal.ofReal (3456 * b * δ ^ 2 / θ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact main_end hδ hb hδb hθ (hv i) (Finset.mem_filter.mp hi).2 (hball i) (hsub i)
      _ ≤ ∑ i : Fin n, ENNReal.ofReal (3456 * b * δ ^ 2 / θ) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal ((n : ℝ) * (3456 * b * δ ^ 2 / θ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (A / 8) := ENNReal.ofReal_le_ofReal hend
  -- the good central mass
  set X := ∑ i, volume (main_good θ (v i) (Y i) Sp ∩ M) with hX
  have hX5 : ENNReal.ofReal (5 * A / 8) ≤ X := by
    have h1 : ENNReal.ofReal (5 * A / 8) + ENNReal.ofReal (3 * A / 8) ≤
        X + ENNReal.ofReal (3 * A / 8) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have h3 : ENNReal.ofReal (3 * A / 8) =
          ENNReal.ofReal (A / 8) + ENNReal.ofReal (A / 8) + ENNReal.ofReal (A / 8) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
      calc ENNReal.ofReal (5 * A / 8 + 3 * A / 8) = ENNReal.ofReal A := by congr 1; ring
        _ ≤ ∑ i, volume (Y i) := hmass
        _ ≤ _ := hdec
        _ ≤ ENNReal.ofReal (A / 8) + ENNReal.ofReal (A / 8) + X + ENNReal.ofReal (A / 8) := by
            gcongr
        _ = X + ENNReal.ofReal (3 * A / 8) := by rw [h3]; ring
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1
  -- the thin slabs
  set V := (Finset.range (⌊2 / b⌋₊ + 1)).filter
      (fun j : ℕ => 2 ≤ j ∧ ((j : ℝ) + 5 / 2) * b ≤ 2) with hV
  set S : ℕ → Set Space := fun j => {q : Space | |q 2 - (-1 + ((j : ℝ) + 1 / 2) * b)| ≤ b / 2}
    with hS
  have hcov : ∀ i, volume (main_good θ (v i) (Y i) Sp ∩ M) ≤
      ∑ j ∈ V, volume (main_good θ (v i) (Y i) Sp ∩ S j) := by
    intro i
    refine (measure_mono ?_).trans (measure_biUnion_finset_le V _)
    rintro q ⟨hq, hqM⟩
    obtain ⟨j, hjV, hj⟩ := main_cover hb hqM.1 hqM.2
    exact mem_iUnion₂.mpr ⟨j, hjV, hq, hj⟩
  have hXV : X ≤ ∑ j ∈ V, ∑ i, volume (main_good θ (v i) (Y i) Sp ∩ S j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => hcov i
  have hVne : V.Nonempty := by
    obtain ⟨j, hjV, -⟩ := main_cover (t := 0) hb (by linarith) (by linarith)
    exact ⟨j, hjV⟩
  have hVcard : (V.card : ℝ) ≤ 3 / b := by
    have h1 : V.card ≤ ⌊2 / b⌋₊ + 1 :=
      (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h2 : (⌊2 / b⌋₊ : ℝ) ≤ 2 / b := Nat.floor_le (by positivity)
    have h3 : (1 : ℝ) ≤ 1 / b := by rw [le_div_iff₀ hb]; linarith
    calc (V.card : ℝ) ≤ (⌊2 / b⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      _ ≤ 2 / b + 1 / b := by linarith
      _ = 3 / b := by ring
  obtain ⟨j, hjV, hj⟩ := main_pigeon (B := 5 * A * b / 24) hVne (hX5.trans hXV) (by
    calc (V.card : ℝ) * (5 * A * b / 24) ≤ 3 / b * (5 * A * b / 24) :=
          mul_le_mul_of_nonneg_right hVcard (by positivity)
      _ = 5 * A / 8 := by field_simp; ring)
  refine ⟨-1 + ((j : ℝ) + 1 / 2) * b, ?_, hj⟩
  obtain ⟨-, hj2, hj3⟩ := Finset.mem_filter.mp hjV
  have hj2' : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hjb : 2 * b ≤ (j : ℝ) * b := mul_le_mul_of_nonneg_right hj2' hb.le
  rw [add_mul] at hj3
  have hlo : -(1 - 2 * b) ≤ -1 + ((j : ℝ) + 1 / 2) * b := by rw [add_mul]; linarith
  have hhi : -1 + ((j : ℝ) + 1 / 2) * b ≤ 1 - 2 * b := by rw [add_mul]; linarith
  have := abs_le.mpr ⟨hlo, hhi⟩
  linarith

/-- A window of length `L` in `[-1, 1]` containing the thin slab. -/
private lemma main_z1 {a b L : ℝ} (hab : |a| + 2 * b ≤ 1) (hb : 0 < b) (hbL : b ≤ L)
    (hL1 : L ≤ 1) :
    ∃ z1 : ℝ, -1 ≤ z1 ∧ z1 + L ≤ 1 ∧ ∀ t : ℝ, |t - a| ≤ b / 2 → t ∈ Icc z1 (z1 + L) := by
  rcases le_or_gt a 0 with ha | ha
  · refine ⟨a - b / 2, ?_, ?_, ?_⟩
    · have := neg_abs_le a; linarith
    · linarith
    · intro t ht; rw [abs_le] at ht; constructor <;> linarith
  · refine ⟨a + b / 2 - L, ?_, ?_, ?_⟩
    · linarith
    · have := le_abs_self a; linarith
    · intro t ht; rw [abs_le] at ht; constructor <;> linarith

/-- If the slope is not `2L`-Lipschitz on the window, its derivative exceeds `L` at `a`. -/
private lemma main_slope {f : ℝ → ℝ} {L a z1 : ℝ} (hf : ContDiff ℝ 2 f)
    (hf2 : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv (deriv f) z| ≤ 1)
    (hz1 : -1 ≤ z1) (hz1L : z1 + L ≤ 1) (ha : a ∈ Icc z1 (z1 + L))
    (hnd : (∀ z ∈ Icc z1 (z1 + L), ∀ z' ∈ Icc z1 (z1 + L),
      |f z - f z'| ≤ 2 * L * |z - z'|) → False) :
    L < |deriv f a| := by
  by_contra hle
  push Not at hle
  apply hnd
  have hJ : Icc z1 (z1 + L) ⊆ Icc (-1) 1 := Icc_subset_Icc hz1 hz1L
  have hlip' := main_lip_of_deriv (convex_Icc (-1 : ℝ) 1) (main_diff_deriv hf) hf2
  apply main_lip_of_deriv (convex_Icc z1 (z1 + L)) (hf.differentiable (by norm_num))
  intro t ht
  have h1 := hlip' t (hJ ht) a (hJ ha)
  have h2 : |t - a| ≤ L := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ha.1, ha.2]
  have h3 := abs_sub_abs_le_abs_sub (deriv f t) (deriv f a)
  linarith

/-- Derivative bounds on the thin slab around `a`. -/
private lemma main_subslab {f : ℝ → ℝ} {a b L : ℝ} (hf : ContDiff ℝ 2 f)
    (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 1)
    (hf2 : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv (deriv f) z| ≤ 1)
    (hab : |a| + 2 * b ≤ 1) (hb : 0 < b) (hbL : 202 * b ≤ L) (hL : L < |deriv f a|) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ 200 * b ≤ m ∧ ∀ t ∈ Icc (a - 2 * b) (a + 2 * b),
      m ≤ |deriv f t| ∧ |deriv f t| ≤ 2 * m ∧ |deriv (deriv f) t| ≤ 1 := by
  have hna := neg_abs_le a
  have hpa := le_abs_self a
  have ha1 : a ∈ Icc (-1 : ℝ) 1 := by rw [mem_Icc]; constructor <;> linarith
  have hlip' := main_lip_of_deriv (convex_Icc (-1 : ℝ) 1) (main_diff_deriv hf) hf2
  have hfa := hf1 a ha1
  refine ⟨|deriv f a| - 2 * b, by linarith, by linarith, by linarith, fun t ht => ?_⟩
  have htI : t ∈ Icc (-1 : ℝ) 1 := by
    rw [mem_Icc] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
  have h1 := hlip' t htI a ha1
  have h2 : |t - a| ≤ 2 * b := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have h3 := abs_sub_abs_le_abs_sub (deriv f t) (deriv f a)
  have h4 := abs_sub_abs_le_abs_sub (deriv f a) (deriv f t)
  rw [abs_sub_comm (deriv f a) (deriv f t)] at h4
  refine ⟨by linarith, by linarith, hf2 t htI⟩

/-- Counting the tubes with dense shading in the thin slab. -/
private lemma main_count {n : ℕ} {v : Fin n → Space} {Y Z : Fin n → Set Space} {S : Set Space}
    {θ U W B : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hZY : ∀ i, Z i ⊆ Y i) (hZ0 : ∀ i, ¬ θ ≤ |v i 2| → Z i = ∅)
    (hUb : ∀ i, θ ≤ |v i 2| → volume (Y i ∩ S) ≤ ENNReal.ofReal U)
    (hB : ENNReal.ofReal B ≤ ∑ i, volume (Z i ∩ S)) :
    ∃ G : Finset (Fin n), (∀ i ∈ G, θ ≤ |v i 2| ∧ ENNReal.ofReal W ≤ volume (Y i ∩ S)) ∧
      B ≤ (G.card : ℝ) * U + n * W := by
  classical
  set G := Finset.univ.filter (fun i => θ ≤ |v i 2| ∧ ENNReal.ofReal W ≤ volume (Y i ∩ S))
    with hG
  refine ⟨G, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  have hterm : ∀ i, volume (Z i ∩ S) ≤
      (if i ∈ G then ENNReal.ofReal U else 0) + ENNReal.ofReal W := by
    intro i
    by_cases hi : i ∈ G
    · rw [ite_eq_left hi]
      have hi' := (Finset.mem_filter.mp hi).2
      calc volume (Z i ∩ S) ≤ volume (Y i ∩ S) :=
            measure_mono (inter_subset_inter_left _ (hZY i))
        _ ≤ ENNReal.ofReal U := hUb i hi'.1
        _ ≤ _ := le_self_add
    · rw [ite_eq_right hi, zero_add]
      by_cases hθ : θ ≤ |v i 2|
      · have h : ¬ ENNReal.ofReal W ≤ volume (Y i ∩ S) := fun h =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ, h⟩)
        exact (measure_mono (inter_subset_inter_left _ (hZY i))).trans (not_le.mp h).le
      · rw [hZ0 i hθ, empty_inter, measure_empty]; exact zero_le
  have hsum : ∑ i, volume (Z i ∩ S) ≤ ENNReal.ofReal ((G.card : ℝ) * U + n * W) := by
    calc ∑ i, volume (Z i ∩ S)
        ≤ ∑ i, ((if i ∈ G then ENNReal.ofReal U else 0) + ENNReal.ofReal W) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ENNReal.ofReal ((G.card : ℝ) * U + n * W) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul,
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hB.trans hsum)

/-- The arithmetic of the count. -/
private lemma main_kap {A b δ θ e N card : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hθ : 0 < θ)
    (he : 0 ≤ e) (hN : 0 ≤ N) (hA : A = e * N * δ ^ 2)
    (h : 5 * A * b / 24 ≤ card * (1152 * (b / 2) * δ ^ 2 / θ) + N * (e / 40 * b * δ ^ 2)) :
    e * θ / 5000 * N ≤ card := by
  have hP : 0 < b * δ ^ 2 := by positivity
  have h1 : (5 * e * N / 24 - N * e / 40) * (b * δ ^ 2) ≤ (card * 576 / θ) * (b * δ ^ 2) := by
    have e1 : 5 * A * b / 24 = (5 * e * N / 24) * (b * δ ^ 2) := by rw [hA]; ring
    have e2 : card * (1152 * (b / 2) * δ ^ 2 / θ) = (card * 576 / θ) * (b * δ ^ 2) := by ring
    have e3 : N * (e / 40 * b * δ ^ 2) = (N * e / 40) * (b * δ ^ 2) := by ring
    rw [e1, e2, e3] at h
    rw [sub_mul]
    linarith
  have h2 := le_of_mul_le_mul_right h1 hP
  have h3 : (11 / 60 * e * N) * θ ≤ card * 576 := by
    have h4 := mul_le_mul_of_nonneg_right h2 hθ.le
    have e4 : card * 576 / θ * θ = card * 576 := by field_simp
    have e5 : (5 * e * N / 24 - N * e / 40) * θ = (11 / 60 * e * N) * θ := by ring
    rw [e4, e5] at h4
    exact h4
  have heN : 0 ≤ e * N * θ := by positivity
  have e6 : e * θ / 5000 * N = (e * N * θ) * (1 / 5000) := by ring
  have e7 : 11 / 60 * e * N * θ = (e * N * θ) * (11 / 60) := by ring
  rw [e7] at h3
  rw [e6]
  have h5 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 5000 ≤ 11 / 60 / 576 by norm_num) heN
  linarith

/-- The packing bound gives `n ≤ δ ^ (-5)`. -/
private lemma main_pack {δ Cp : ℝ} {n : ℕ} (hδ : 0 < δ) (hn : (n : ℝ) * δ ^ 4 ≤ Cp)
    (hC : Cp * δ ≤ 1) : (n : ℝ) ≤ δ ^ (-5 : ℝ) := by
  have h5 : (n : ℝ) * δ ^ 5 ≤ 1 := by
    calc (n : ℝ) * δ ^ 5 = ((n : ℝ) * δ ^ 4) * δ := by ring
      _ ≤ Cp * δ := mul_le_mul_of_nonneg_right hn hδ.le
      _ ≤ 1 := hC
  rw [Real.rpow_neg hδ.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← one_div, le_div_iff₀ (by positivity)]
  exact h5

/-- Horizontal slabs are measurable. -/
private lemma main_slab_meas (a r : ℝ) : MeasurableSet {q : Space | |q 2 - a| ≤ r} :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- The normalized nonsingular examples at a fixed positive optimal deficit `σ`. -/
theorem normalized_examples {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hupper : ∀ t : ℝ, σ < t → ¬ Extremal t) (hgrains : Grains σ) :
    NormalizedExamples σ := by
  intro ηs d0 hηs hd0
  obtain ⟨KNH, -, hNH⟩ := near_horizontal_mass
  obtain ⟨KND, hKND, hND⟩ := nondegenerate
  obtain ⟨KR, -, hR⟩ := rescale
  obtain ⟨Cp, hCp, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  -- exponents
  obtain ⟨η1, hη1def⟩ : ∃ η1 : ℝ, η1 = min ηs (1 / 100) := ⟨_, rfl⟩
  have hη1 : 0 < η1 := by rw [hη1def]; exact lt_min hηs (by norm_num)
  have hη1s : η1 ≤ ηs := by rw [hη1def]; exact min_le_left _ _
  have hη1' : η1 ≤ 1 / 100 := by rw [hη1def]; exact min_le_right _ _
  obtain ⟨ε2, hε2⟩ : ∃ ε2 : ℝ, ε2 = η1 / 100 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ ^ 2 * ε2 / 100 := ⟨_, rfl⟩
  obtain ⟨εe, hεe⟩ : ∃ εe : ℝ, εe = c / 10 := ⟨_, rfl⟩
  have hε2p : 0 < ε2 := by rw [hε2]; positivity
  have hε2s : ε2 ≤ 1 / 10000 := by rw [hε2]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hεe0 : 0 < εe := by rw [hεe]; positivity
  obtain ⟨η0, de, hη0, hde, hlower⟩ := uniform_volume_lower_mono hupper hεe0
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (η0 / 2) (σ * c / 200) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min (by positivity) (by positivity)
  have hηη0 : η ≤ η0 / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηc : η ≤ σ * c / 200 := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨d, hd, hcut⟩ := main_params (KNH := KNH) (KR := KR) hσ hσ1 hη1 hη1' hε2 hc hεe hη
    hηη0 hηc hde hd0 (by linarith : (0 : ℝ) ≤ KND) hCp.le
  -- the grains example
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hD, hS, hcpt, -, f, P, hf, hAD, -, hPn, -, hloc⟩ :=
    hgrains η d hη hd
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP10, hP11, hP12, hP13, hP15, hP16, hP17,
    hP18⟩ := hcut δ hδ hδd
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨hn, hvu, hball, hsep, hmeas, hsub, hmass⟩ := hD
  have hfam : Family δ n x v Y := ⟨hvu, hball, hmeas, hsub⟩
  have hGC : GlobalCount η δ n x v := globalCount_of_strong hδ hδ1 hS
  obtain ⟨hfC, hfb⟩ := hf
  have hfc : Continuous f := hfC.continuous
  have hf0 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1 := fun z hz => (hfb z hz).1
  have hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 1 := fun z hz => (hfb z hz).2.1
  have hf2 : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv (deriv f) z| ≤ 1 := fun z hz => (hfb z hz).2.2
  have hflip : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'| := by
    intro z hz z' hz'
    simpa using main_lip_of_deriv (convex_Icc _ _) (hfC.differentiable (by norm_num)) hf1
      z hz z' hz'
  have hE : (⋃ i, Y i) ⊆ ball 0 1 := iUnion_subset fun i => (hsub i).trans (hball i)
  have hs : ∀ z ∈ Icc (-1 : ℝ) 1,
      volume (PS f (⋃ i, Y i) z) ≤ ENNReal.ofReal (8 * δ ^ (σ - η)) :=
    fun z hz => volume_le_eight_rpow hδ hδ1 hσ.le hσ1.le (ps_subset_interval hE (hf0 z hz))
      (hAD z hz)
  -- basic facts about the parameters
  have hθ0 : 0 < δ ^ c := Real.rpow_pos_of_pos hδ c
  have hθ1 : δ ^ c ≤ 1 := Real.rpow_le_one hδ.le hδ1 hc0.le
  have hL0 : 0 < δ ^ ε2 := Real.rpow_pos_of_pos hδ ε2
  have hL1 : δ ^ ε2 ≤ 1 := Real.rpow_le_one hδ.le hδ1 hε2p.le
  have hδθ : δ ≤ δ ^ c := by linarith
  have hb0 : 0 < δ ^ ε2 / 1000 := by positivity
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
  -- Step 1: sparse grains carry little mass
  have hSpm : MeasurableSet (main_sp f (⋃ i, Y i) (δ ^ (εe + η) / 32)) :=
    sparse_measurableSet hfc (MeasurableSet.iUnion hmeas) _
  have hSp := main_sparse (lam := δ ^ (εe + η) / 32) hlower hδ hP3 hδ100 (by linarith)
    ⟨hn, hvu, hball, hsep, hmeas, hsub, hmass⟩ hS hfc (by positivity) (by positivity) hs (by
      have h : δ ^ (εe + η) * δ ^ (σ - η) = δ ^ (σ + εe) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      refine le_of_eq ?_
      calc 2 * (δ ^ (εe + η) / 32) * (8 * δ ^ (σ - η)) = δ ^ (εe + η) * δ ^ (σ - η) / 2 := by
            ring
        _ = δ ^ (σ + εe) / 2 := by rw [h])
  have hSp' : ∑ i, volume (Y i ∩ main_sp f (⋃ i, Y i) (δ ^ (εe + η) / 32)) ≤
      ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 8) := by
    refine hSp.le.trans (ENNReal.ofReal_le_ofReal ?_)
    calc δ ^ η0 * n * δ ^ 2 = δ ^ η0 * (n * δ ^ 2) := by ring
      _ ≤ δ ^ η / 8 * (n * δ ^ 2) := mul_le_mul_of_nonneg_right hP4 hsq
      _ = δ ^ η * n * δ ^ 2 / 8 := by ring
  -- Step 2: nearly horizontal tubes carry little mass
  have hNH' : ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < δ ^ c), volume (Y i) ≤
      ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 8) := by
    refine (hNH σ η (δ ^ c) δ hσ hσ1 hη hδ hδ100 hδθ hP6 n x v Y hfam hGC f hfc hf0 hflip
      hAD).trans (ENNReal.ofReal_le_ofReal ?_)
    calc KNH * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4) * n * δ ^ 2
        = KNH * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4) * (n * δ ^ 2) := by
          ring
      _ ≤ δ ^ η / 8 * (n * δ ^ 2) := mul_le_mul_of_nonneg_right hP5 hsq
      _ = δ ^ η * n * δ ^ 2 / 8 := by ring
  -- Step 3: a thin slab with a fair share of the good mass
  obtain ⟨a, ha, hma⟩ := main_mass (Sp := main_sp f (⋃ i, Y i) (δ ^ (εe + η) / 32))
    (θ := δ ^ c) (b := δ ^ ε2 / 1000) (A := δ ^ η * n * δ ^ 2) hδ hb0 (by linarith)
    (by linarith) hθ0 (by positivity) hvu hball hsub hmass hSp' hNH' (by
      calc (n : ℝ) * (3456 * (δ ^ ε2 / 1000) * δ ^ 2 / δ ^ c)
          = 3456 * (δ ^ ε2 / 1000) / δ ^ c * (n * δ ^ 2) := by ring
        _ ≤ δ ^ η / 8 * (n * δ ^ 2) := mul_le_mul_of_nonneg_right hP7 hsq
        _ = δ ^ η * n * δ ^ 2 / 8 := by ring)
  -- Step 4: the slope is nondegenerate near the slab
  obtain ⟨z1, hz1, hz1L, hz1S⟩ := main_z1 ha hb0 (by linarith) hL1
  have hδL2 : δ ≤ (δ ^ ε2) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (ε2 * ((2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by push_cast; linarith)
  have hL : δ ^ ε2 < |deriv f a| := by
    refine main_slope hfC hf2 hz1 hz1L (hz1S a (by simp only [sub_self, abs_zero]; positivity))
      (fun hlip => hND σ η δ (δ ^ c) (δ ^ ε2) (δ ^ (εe + η) / 32) (δ ^ η / 5000) z1 hσ hσ1 hη
        hδ hδ100 hθ0 hθ1 (by positivity) ?_ (by positivity) ?_ hP8 hδL2 hP10 hz1 hz1L hP11 hP12
        n x v Y hn hfam hGC f P hfc hf0 hlip hAD hPn hloc
        (fun i => main_good (δ ^ c) (v i) (Y i) (main_sp f (⋃ i, Y i) (δ ^ (εe + η) / 32)) ∩
          {q : Space | |q 2 - a| ≤ δ ^ ε2 / 1000 / 2})
        (fun i => (main_good_meas (hmeas i) hSpm).inter (main_slab_meas _ _))
        (fun i => inter_subset_left.trans main_good_sub)
        (fun i hi => by
          by_contra h
          rw [main_good_empty h, empty_inter] at hi
          exact not_nonempty_empty hi)
        (fun i q hq => hz1S _ hq.2)
        (fun i => inter_subset_left.trans (main_good_full i)) ?_)
    · have : δ ^ (εe + η) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
      linarith
    · have : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
      linarith
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hma
      have h0 : 0 ≤ δ ^ η * n * δ ^ 2 * δ ^ ε2 := by positivity
      have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 5000 ≤ 5 / 24000 by norm_num) h0
      calc δ ^ η / 5000 * n * δ ^ ε2 * δ ^ 2 = δ ^ η * n * δ ^ 2 * δ ^ ε2 * (1 / 5000) := by
            ring
        _ ≤ δ ^ η * n * δ ^ 2 * δ ^ ε2 * (5 / 24000) := h1
        _ = 5 * (δ ^ η * n * δ ^ 2) * (δ ^ ε2 / 1000) / 24 := by ring
  -- Step 5: derivative bounds on the thin slab
  obtain ⟨m, hm0, hm1, hm200, hmder⟩ := main_subslab hfC hf1 hf2 ha hb0 (by linarith) hL
  -- Step 6: many tubes with dense shading in the thin slab
  obtain ⟨G, hGmem, hcnt⟩ := main_count (v := v) (Y := Y)
    (Z := fun i => main_good (δ ^ c) (v i) (Y i) (main_sp f (⋃ i, Y i) (δ ^ (εe + η) / 32)))
    (S := {q : Space | |q 2 - a| ≤ δ ^ ε2 / 1000 / 2}) (θ := δ ^ c)
    (U := 1152 * (δ ^ ε2 / 1000 / 2) * δ ^ 2 / δ ^ c)
    (W := δ ^ η / 40 * (δ ^ ε2 / 1000) * δ ^ 2)
    (B := 5 * (δ ^ η * n * δ ^ 2) * (δ ^ ε2 / 1000) / 24) (by positivity) (by positivity)
    (fun i => main_good_sub) (fun i h => main_good_empty h)
    (fun i h => (measure_mono (inter_subset_inter_left _ (hsub i))).trans
      (main_slab_le hδ (by linarith) hθ0 (hvu i) h)) hma
  have hGcard : δ ^ (η + c) / 5000 * n ≤ G.card := by
    have h := main_kap (A := δ ^ η * n * δ ^ 2) (b := δ ^ ε2 / 1000) (δ := δ) (θ := δ ^ c)
      (e := δ ^ η) (N := n) (card := G.card) hb0 hδ hθ0 (by positivity) hnn rfl hcnt
    rw [Real.rpow_add hδ]; exact h
  -- Step 7: rescale
  have hδη1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
  have hδηc1 : δ ^ (η + c) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  obtain ⟨n', x', v', Y', hD', hcpt', hv', hGC', g, hg, hgs⟩ := hR η η1 δ (δ ^ c) a
    (δ ^ ε2 / 1000) m (δ ^ η / 40) (δ ^ (η + c) / 5000) (8 * δ ^ (σ - η)) hη hη1 hδ hδ100 hθ0
    hθ1 hP13 hb0 (by linarith) hP15 hm0 hm1 hm200 ha (by positivity) (by linarith)
    (by positivity) (by linarith) (by positivity) hP16 n x v Y hn
    (main_pack hδ (hpack δ hδ hδ100 n x v hvu hball hsep) hP17) hfam hcpt hGC f hfC hmder
    (fun z hz => hs z ⟨by linarith [hz.1, neg_abs_le a], by linarith [hz.2, le_abs_self a]⟩)
    G hGcard (fun i hi => (hGmem i hi).1) (fun i hi => (hGmem i hi).2)
  have hδ'0 : 0 < 4 * δ / δ ^ c := by positivity
  have hδ'1 : 4 * δ / δ ^ c ≤ 1 := by linarith
  refine ⟨4 * δ / δ ^ c, hδ'0, hP1, hP2, n', x', v', Y', dense_mono_error hδ'0 hδ'1 hη1s hD',
    hcpt', hv', hGC'.mono_error hδ'0 hδ'1 hη1s, g, hg,
    fun z hz => (hgs z hz).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hδδ' : δ ≤ 4 * δ / δ ^ c := by
    rw [le_div_iff₀ hθ0]
    calc δ * δ ^ c ≤ δ * 1 := mul_le_mul_of_nonneg_left hθ1 hδ.le
      _ ≤ 4 * δ := by linarith
  have hpow : δ ^ (σ / 8) ≤ (4 * δ / δ ^ c) ^ (σ / 8) :=
    Real.rpow_le_rpow hδ.le hδδ' (by positivity)
  have hpos : 0 ≤ δ ^ (σ / 8) := by positivity
  linarith

end WangZahlLot.Obl.wz_grains_nonsingular_slices
