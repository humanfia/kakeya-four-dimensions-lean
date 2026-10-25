import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeCount
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ScalarNumerics
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.Table

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Lib.K4FullTimeLayers

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The original child count and original parent comparison supply scalar
support on any later labeled event. No floor is required in that event's law. -/
theorem nested_original_scalar_support {k : ℕ} {s₀ s₁ D τ v : ℝ}
    (parent : cfg.AssignmentLevel k s₀) (child : cfg.AssignmentLevel k s₁)
    (P : NativeAffineTable cfg k s₀) (L : NativeAffineTable cfg k s₁)
    (C : RawChart α) (j₀ : Fin (cfg.n k s₀))
    (S : Finset (Fin (cfg.n k s₁))) (J : Fin (2 ^ cfg.T k s₁))
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1)
    (hs₁ : 0 ≤ s₁) (hst : s₀ ≤ s₁)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hlarge : 69120 * cfg.K k ^ 8 ≤ cfg.N k)
    (hD : 0 < D) (hDq : D ≤ cfg.timeLength k s₁ ^ 2)
    (ht : τ ∈ Icc (0 : ℝ) 1)
    (hblock : ∀ i ∈ S, cfg.j k s₁ i = J)
    (hA : ∀ i ∈ S, cfg.A k s₁ i ⊆ cfg.A k s₀ j₀)
    (hI : ∀ i ∈ S, Data.I (cfg.T k s₁) (cfg.j k s₁ i) ⊆
      Data.I (cfg.T k s₀) (cfg.j k s₀ j₀))
    (hv : |v| ≤ cfg.K k ^ 2)
    (hcontact : ∀ i ∈ S, ∃ z ∈ cfg.originalTrueBox k s₁ i,
      |z 1 - referenceZ ![(C.q 1 : ℝ) * D, (C.q 2 : ℝ) * D, v] (z 0)| ≤ cfg.K k ^ 2 * D ∧
      |z 2 - referenceY ![(C.q 1 : ℝ) * D, (C.q 2 : ℝ) * D, v] (z 0)| ≤ cfg.K k ^ 2 * D)
    (hmesh₀ : cfg.N k ^ (-(s₁ + 2)) ≤ cfg.timeLength k s₁ / 2)
    (hmesh₁ : (|v| + 1) * cfg.N k ^ (-(s₁ + 2)) ≤
      8 * cfg.K k ^ 2 * cfg.timeLength k s₁)
    (hmesh₂ : (|-(C.q 1 : ℝ) * D -
        ((((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s₁) * v| +
        |(((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s₁| + 1) *
        cfg.N k ^ (-(s₁ + 2)) ≤ 32 * cfg.K k ^ 4 * cfg.timeLength k s₁ ^ 2)
    (hresolve : cfg.N k ^ (-(s₁ + 2)) * ∑ e : Fin 3, |P.entry j₀ e.succ| ≤
      cfg.N k ^ (-s₀))
    (hcap : ∀ s ∈ ({s₀, s₁} : Set ℝ), ∀ (Q : Fin 3 → ℤ) (j : ℤ),
      cfg.μ k {ω | cfg.z k (cfg.N k) (s₁ + 2) ω = Q ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-s)⌋ = j} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * (s₁ + 2) - cfg.d * s)))
    (hF : C.F τ = normalizedRow (liftAffine (P.entry j₀) v) C.h D (cfg.N k ^ (-s₀)) τ)
    (hcoords : ∀ l, (l, τ) ∈ C.E → l ∈ C.A ∧
      |cfg.b k l 0 - (C.q 1 : ℝ) * D| ≤ D ∧ |cfg.b k l 1 - (C.q 2 : ℝ) * D| ≤ D)
    (hvel : ∀ l, (l, τ) ∈ C.E → |cfg.b k l 3 - v| ≤ cfg.N k ^ (-cfg.e₀))
    (hdef : ∀ l, (l, τ) ∈ C.E → |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-cfg.e₀))
    (hcover : ∀ l, (l, τ) ∈ C.E → ∃ i ∈ S,
      l ∈ cfg.B k s₁ i ∧ τ ∈ Data.I (cfg.T k s₁) (cfg.j k s₁ i))
    (hcontactBudget : 16 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-s₁))
    (hroom : 14155776 * cfg.K k ^ 10 * D ≤
      (cfg.N k ^ (-s₁) / cfg.N k ^ (-s₀)) * cfg.timeLength k s₁ ^ 2) :
    ∃ Γ : Finset ℤ,
      (Γ.card : ℝ) ≤ 811008 * cfg.K k ^ 12 *
        (cfg.N k ^ (-s₁) / cfg.N k ^ (-s₀)) ^ (-cfg.d) ∧
      ∀ l, (l, τ) ∈ C.E →
        ⌊FirstJet.scal (C.y (cfg.b k) (cfg.N k ^ (-s₀)) D)
          (C.β (cfg.b k) (cfg.N k ^ (-s₀)) D)
          (C.γ (cfg.b k) (cfg.N k ^ (-s₀)) D) C.F l τ /
            (cfg.N k ^ (-s₁) / cfg.N k ^ (-s₀))⌋ ∈ Γ := by
  have hNp : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have ha₀ : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hNp _
  have ha₁ : 0 < cfg.N k ^ (-s₁) := Real.rpow_pos_of_pos hNp _
  have hq : 0 < cfg.timeLength k s₁ := by unfold Data.timeLength; positivity
  have hw : 0 < cfg.N k ^ (-s₁) / cfg.N k ^ (-s₀) := div_pos ha₁ ha₀
  have hwidth : cfg.N k ^ (-s₀) * (cfg.N k ^ (-s₁) / cfg.N k ^ (-s₀)) =
      cfg.N k ^ (-s₁) := mul_div_cancel₀ _ ha₀.ne'
  obtain ⟨hH, hm₀, hm₁, hmfit, hfine⟩ :=
    cfg.original_affine_mesh_resolves child hN hK hℓ hκ hκ1 hs₁ hlarge
  have hcount := cfg.original_contact_child_count parent child hν hNp hK hℓ hdom
    j₀ S J hblock rfl hA hI
    ![(C.q 1 : ℝ) * D, (C.q 2 : ℝ) * D, v] hv hDq hcontact
    (P.entry j₀) (P.original_fit j₀) (Real.rpow_pos_of_pos hNp _)
    hmesh₀ hmesh₁
    (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_mul]
      using hmesh₂) hresolve
    (cfg.original_hidden_cell_cap hNp (hcap s₀ (by simp)))
  have hdifference (i : Fin (cfg.n k s₁)) (hi : i ∈ S) :
      |L.entry i 2 - P.entry j₀ 2| ≤
        2359296 * cfg.K k ^ 10 * cfg.N k ^ (-s₀) / cfg.timeLength k s₁ ^ 2 ∧
      |L.entry i 3 - P.entry j₀ 3| ≤
        2359296 * cfg.K k ^ 10 * cfg.N k ^ (-s₀) / cfg.timeLength k s₁ ^ 2 := by
    have hcompare := cfg.compare_nested_affine_tables parent child hν hN1 hK hℓ hst hdom
      i j₀ (hA i hi) (hI i hi) (L.entry i) (P.entry j₀) (L.slopes i)
      (L.original_fit i) (P.original_fit j₀) (hcap s₁ (by simp))
      hH hm₀ hm₁ hmfit hfine
    obtain ⟨z, hz, _, _⟩ := hcontact i hi
    have hg := cfg.ordinary_spatial_slopes_at_trueBox_point hK
      (by positivity : 0 ≤ 262144 * cfg.K k ^ 9 * cfg.N k ^ (-s₀))
      i (L.entry i) (P.entry j₀) z hz (hcompare.2 z hz)
    convert hg using 1 <;> congr 1 <;> ring
  apply C.scalar_support_with_native_budgets (cfg.b k) (P.entry j₀) L.entry S
    hK hD ha₀ hw hq ht hF hcount hcoords hvel hdef
    (fun i _ => ⟨L.slopes i 1, L.slopes i 2⟩) hdifference
  · intro l hl
    obtain ⟨i, hi, hli, hti⟩ := hcover l hl
    exact ⟨i, hi, by simpa only [hwidth] using L.fit i l hli τ hti⟩
  · simpa only [hwidth] using hcontactBudget
  · exact hroom

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
