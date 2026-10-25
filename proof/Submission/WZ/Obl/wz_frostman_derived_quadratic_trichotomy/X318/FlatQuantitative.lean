-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatQuantitative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatAssembly
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Reduction

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FlatQuantitative.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma mul_rpow_le_of_absorbed {δ C α β : ℝ} (hδ : 0 < δ)
    (h : C * δ ^ (α - β) ≤ 1) : C * δ ^ α ≤ δ ^ β := by
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hδ.le β)
  have he : δ ^ (α - β) * δ ^ β = δ ^ α := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  simpa only [mul_assoc, he, one_mul] using hh

lemma factor_error_bounds {δ ν ζ ζ₃ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hsmall : 8192 * δ ^ (ζ₃ - ζ - 4 * ν) ≤ 1) :
    32 * δ ^ (-ν) * δ ^ (-ν) ≤ δ ^ (-ζ₃) ∧
    2048 * (δ ^ (-ν) * δ ^ (-ν)) ^ 2 ≤ δ ^ (-ζ₃) ∧
    8192 * δ ^ (-ζ) * (δ ^ (-ν) * δ ^ (-ν)) ^ 2 ≤ δ ^ (-ζ₃) := by
  have h₂ : δ ^ (-ν) * δ ^ (-ν) = δ ^ (-(2 * ν)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have h₄ : (δ ^ (-ν) * δ ^ (-ν)) ^ 2 = δ ^ (-(4 * ν)) := by
    rw [h₂, ← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  have hζ₄ : δ ^ (-ζ) * (δ ^ (-ν) * δ ^ (-ν)) ^ 2 = δ ^ (-ζ - 4 * ν) := by
    rw [h₄, ← Real.rpow_add hδ]
    congr 1
  have hsmall₂ : 32 * δ ^ (ζ₃ - 2 * ν) ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show ζ₃ - ζ - 4 * ν ≤ ζ₃ - 2 * ν by linarith)
    have hz := Real.rpow_nonneg hδ.le (ζ₃ - ζ - 4 * ν)
    nlinarith
  have hsmall₄ : 2048 * δ ^ (ζ₃ - 4 * ν) ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show ζ₃ - ζ - 4 * ν ≤ ζ₃ - 4 * ν by linarith)
    have hz := Real.rpow_nonneg hδ.le (ζ₃ - ζ - 4 * ν)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, h₂]
    apply mul_rpow_le_of_absorbed hδ
    convert hsmall₂ using 1 <;> congr 2 <;> ring
  · rw [h₄]
    apply mul_rpow_le_of_absorbed hδ
    convert hsmall₄ using 1 <;> congr 2 <;> ring
  · rw [mul_assoc, hζ₄]
    apply mul_rpow_le_of_absorbed hδ
    convert hsmall using 1 <;> congr 2 <;> ring

lemma flatness_after_normalizing {δ ζ₂ a b : ℝ} (hδ : 0 < δ)
    (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hflat : a ≤ δ ^ (ζ₂ / 100) * b) (hsmall : 2 * δ ^ (ζ₂ / 200) ≤ 1) :
    min a 1 ≤ δ ^ (ζ₂ / 200) * min b 1 := by
  let s := δ ^ (ζ₂ / 200)
  have hs : 0 ≤ s := Real.rpow_nonneg hδ.le _
  have he : δ ^ (ζ₂ / 100) = s ^ 2 := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  have hb : b ≤ 2 * min b 1 := by
    have hh : b / 2 ≤ min b 1 := le_min (by linarith) (by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
  have hs' := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hs (le_min hb0 zero_le_one))
  rw [he] at hflat
  exact (min_le_left _ _).trans (by dsimp [s] at *; nlinarith only [hflat, hm, hs'])

/-- The part of the convex factorization output needed in the flat alternative. -/
def LongFactor (ν δ a b : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ δ ^ ν * n ≤ k ∧
    ∃ c : ℝ, 1 ≤ c ∧ KatzTao δ c (fun i => A (g i)) ∧
      ∃ (p : ℕ) (W : Fin p → Set Space),
        (∀ j, ∃ e : Space ≃ᵃⁱ[ℝ] Space,
          W j = e '' {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2}) ∧
        (∀ i, ∃ j, A (g i) ⊆ W j) ∧
        (∀ i, (ncard {j | A (g i) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
        (∀ j, δ ^ ν * c * a * b ≤
          (contained (fun i => A (g i)) (W j) : ℝ) * δ ^ 2)

/-- Including both refinements and every explicit power loss, a flat output of
convex factorization gives the required retained subfamily in branch (C). -/
theorem flat_refinement_of_long_factor {n : ℕ} (A : Fin n → Set Space)
    {ν δ ζ ζ₂ ζ₃ θ a b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hδa : δ ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2)
    (hflat : a ≤ δ ^ (ζ₂ / 100) * b)
    (hscale : 2 * δ ^ (ζ₂ / 200) ≤ 1)
    (herror : 8192 * δ ^ (ζ₃ - ζ - 5 * ν) ≤ 1)
    (hretain : 4 * δ ^ (θ - ν) ≤ 1)
    (hball : ∀ i, A i ⊆ Metric.ball (0 : Space) 1)
    (hF : Frostman (δ ^ (-ζ)) A) (hfactor : LongFactor ν δ a b A) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
      FlatPrisms ζ₂ ζ₃ δ (fun i => A (g i)) := by
  classical
  obtain ⟨k, g, hg, hk, hsize, c, hc, hKT, p, W, hshape, hcov, hdeg, hsat⟩ := hfactor
  have hprod : δ ^ (-ν) * δ ^ ν = 1 := by rw [← Real.rpow_add hδ]; simp
  have hsize' : (n : ℝ) ≤ δ ^ (-ν) * k := by
    have hh := mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hδ.le (-ν))
    simpa only [← mul_assoc, hprod, one_mul] using hh
  have hFg : Frostman (δ ^ (-(ζ + ν))) (fun i => A (g i)) := by
    have he : δ ^ (-ζ) * δ ^ (-ν) = δ ^ (-(ζ + ν)) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    simpa only [he] using hF.restrict (Real.rpow_nonneg hδ.le _) g hg hsize'
  have hsat' (j) : c * a * b ≤ δ ^ (-ν) *
      (contained (fun i => A (g i)) (W j) : ℝ) * δ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hsat j) (Real.rpow_nonneg hδ.le (-ν))
    simpa only [← mul_assoc, hprod, one_mul] using hh
  have herr : 8192 * δ ^ (ζ₃ - (ζ + ν) - 4 * ν) ≤ 1 := by
    convert herror using 1 <;> congr 2 <;> ring
  obtain ⟨hE₁, hE₂, hE₃⟩ := factor_error_bounds hδ hδ1 hν (add_nonneg hζ hν) herr
  have hf := flatness_after_normalizing hδ (hδ.le.trans (hδa.trans hab)) hb2 hflat hscale
  obtain ⟨m, f, hf', hmass, hC⟩ := flat_prisms_of_saturated_cover (fun i => A (g i)) W
    hδ hδ1 hδa hab hb2 hf hk (by linarith : 0 < c)
    (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) (Real.rpow_nonneg hδ.le _)
    hE₁ hE₂ hE₃ (fun i => hball _) hFg hKT hshape hcov hdeg hsat'
  refine ⟨m, g ∘ f, hg.comp hf', ?_, hC⟩
  have hp : 4 * δ ^ θ ≤ δ ^ ν := mul_rpow_le_of_absorbed hδ hretain
  have hh := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n)
  nlinarith only [hh, hsize, hmass]

theorem output_of_flat_long_factor {n : ℕ} (A : Fin n → Set Space)
    {ν δ ζ ζ₁ ζ₂ ζ₃ θ a b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hδa : δ ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2)
    (hflat : a ≤ δ ^ (ζ₂ / 100) * b)
    (hscale : 2 * δ ^ (ζ₂ / 200) ≤ 1)
    (herror : 8192 * δ ^ (ζ₃ - ζ - 5 * ν) ≤ 1)
    (hretain : 4 * δ ^ (θ - ν) ≤ 1)
    (hball : ∀ i, A i ⊆ Metric.ball (0 : Space) 1)
    (hF : Frostman (δ ^ (-ζ)) A) (hfactor : LongFactor ν δ a b A) :
    Output ζ₁ ζ₂ ζ₃ δ θ A := by
  obtain ⟨k, g, hg, hsize, hC⟩ := flat_refinement_of_long_factor A
    hδ hδ1 hν hζ hδa hab hb2 hflat hscale herror hretain hball hF hfactor
  exact ⟨k, g, hg, hsize, Or.inr hC⟩

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
