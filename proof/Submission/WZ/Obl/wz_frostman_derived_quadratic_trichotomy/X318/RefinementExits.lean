-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.RefinementExits.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatQuantitative

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file RefinementExits.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma Frostman.restrict_power {n k : ℕ} {A : Fin n → Set Space} {δ ζ ν : ℝ}
    (hδ : 0 < δ) (hF : Frostman (δ ^ (-ζ)) A)
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hsize : δ ^ ν * n ≤ k) :
    Frostman (δ ^ (-(ζ + ν))) (fun i => A (g i)) := by
  have hprod : δ ^ (-ν) * δ ^ ν = 1 := by rw [← Real.rpow_add hδ]; simp
  have hsize' : (n : ℝ) ≤ δ ^ (-ν) * k := by
    have hh := mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hδ.le (-ν))
    simpa only [← mul_assoc, hprod, one_mul] using hh
  have he : δ ^ (-ζ) * δ ^ (-ν) = δ ^ (-(ζ + ν)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  simpa only [he] using hF.restrict (Real.rpow_nonneg hδ.le _) g hg hsize'

/-- The retention exponents add when an output is lifted through a refinement. -/
lemma Output.lift {n k : ℕ} {A : Fin n → Set Space} {δ ζ₁ ζ₂ ζ₃ θ ν : ℝ}
    (hδ : 0 < δ) (g : Fin k → Fin n) (hg : Function.Injective g)
    (hsize : δ ^ ν * n ≤ k)
    (h : Output ζ₁ ζ₂ ζ₃ δ θ (fun i => A (g i))) :
    Output ζ₁ ζ₂ ζ₃ δ (θ + ν) A := by
  obtain ⟨m, f, hf, hm, hout⟩ := h
  refine ⟨m, g ∘ f, hg.comp hf, ?_, hout⟩
  calc
    δ ^ (θ + ν) * n = δ ^ θ * (δ ^ ν * n) := by
      rw [Real.rpow_add hδ]
      ring
    _ ≤ δ ^ θ * k := mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hδ.le _)
    _ ≤ m := hm

lemma Output.mono_retention {n : ℕ} {A : Fin n → Set Space}
    {δ ζ₁ ζ₂ ζ₃ θ θ' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : θ ≤ θ')
    (h : Output ζ₁ ζ₂ ζ₃ δ θ A) : Output ζ₁ ζ₂ ζ₃ δ θ' A := by
  obtain ⟨k, g, hg, hsize, hout⟩ := h
  refine ⟨k, g, hg, ?_, hout⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hθ) (Nat.cast_nonneg n)).trans hsize

/-- A retained family with the target KT constant already gives branch (B).
The Frostman hypothesis is inherited with exactly the retention power lost. -/
theorem output_of_katz_tao_refinement {δ ζ ζ₁ ζ₂ ζ₃ ν θ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hζ₁ : ζ₁ ≤ 1) (hζ₂ : 0 ≤ ζ₂)
    (hνθ : ν ≤ θ) (habsorb : 384 * δ ^ (ζ₂ - (ζ + ν)) ≤ 1)
    {n k : ℕ} (x v : Fin n → Space) (g : Fin k → Fin n)
    (hg : Function.Injective g) (hk : 0 < k) (hsize : δ ^ ν * n ≤ k)
    (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)))
    (hKT : KatzTao δ (δ ^ (-ζ₂)) (fun i => Tube δ (x (g i)) (v (g i)))) :
    Output ζ₁ ζ₂ ζ₃ δ θ (fun i => Tube δ (x i) (v i)) := by
  refine ⟨k, g, hg, ?_, Or.inl ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le hνθ) (Nat.cast_nonneg n)).trans hsize
  · exact separated_scales_of_frostman_and_katz_tao hδ hδ1 hζ₁ hζ₂ habsorb
      (fun i => x (g i)) (fun i => v (g i)) hk (fun i => hv _)
      (fun i => hball _) (fun i j hij => hsep _ _ (hg.ne hij))
      (hF.restrict_power hδ g hg hsize) hKT

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
