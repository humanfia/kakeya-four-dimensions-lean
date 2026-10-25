/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/TrueDomainCounting.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomains
import Submission.Obl.k4_general_parent_projected_layers.Support.WeightedTerminalBudget

/-! The weighted common-domain count for true packets, with the original velocity law. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

noncomputable section

/-- One true packet's common-domain menu has a reference budget proportional to
`Q³g`. Major velocity bins are summed with their ORIGINAL probability weights. -/
theorem true_domain_reference_menu
    (J V : Finset ℤ) (I : ℤ → Finset ℤ) (G : ℤ → ℤ → Finset (ℤ × ℤ))
    (P : ℤ → ℤ → ℤ → Finset ℤ)
    {K Q q χ g m : ℝ} (hK : 0 ≤ K) (hQ : 0 < Q) (hq : 0 < q)
    (hχ : 0 < χ) (hg : 0 < g) (hm : 0 < m)
    (hJ : (J.card : ℝ) * q ≤ 6 * Q)
    (hI : ∀ v, ((I v).card : ℝ) * χ ≤ 10 * K * Q)
    (hG : ∀ v z, ((G v z).card : ℝ) ≤ 180 * K ^ 2)
    (hP : ∀ j v z, ((P j v z).card : ℝ) * m ≤ 22 * K * Q * g) :
    ∃ S : Finset Code,
      (∀ w : ℤ → ℝ, (∀ v, 0 ≤ w v) → (∑ v ∈ V, w v) ≤ 1 →
        (∑ c ∈ S, q * χ * m * w (c 1)) ≤ 237600 * K ^ 4 * Q ^ 3 * g) ∧
      ∀ j ∈ J, ∀ v ∈ V, ∀ z ∈ I v, ∀ γ ∈ G v z, ∀ p ∈ P j v z,
        (![j, v, z, γ.2, p] : Code) ∈ S := by
  classical
  let Index := Σ _j : ℤ, Σ _v : ℤ, Σ _z : ℤ, Σ _γ : ℤ × ℤ, ℤ
  let D : Finset Index := J.sigma fun j => V.sigma fun v =>
    (I v).sigma fun z => (G v z).sigma fun _γ => P j v z
  let decode (i : Index) : Code := ![i.1, i.2.1, i.2.2.1, i.2.2.2.1.2, i.2.2.2.2]
  let S : Finset Code := D.image decode
  refine ⟨S, ?_, ?_⟩
  · intro w hw hwsum
    have hper (j : ℤ) :
        (∑ v ∈ V, ∑ z ∈ I v, ∑ γ ∈ G v z, ∑ _p ∈ P j v z, q * χ * m * w v) ≤
          39600 * K ^ 4 * q * Q ^ 2 * g := by
      let T : ℤ → ℤ → ℤ × ℤ → ℝ := fun v z _ => (P j v z).card * q * m / g
      have harea (v z : ℤ) (γ : ℤ × ℤ) : T v z γ ≤ (22 * K * q / Q) * Q ^ 2 := by
        calc
          _ = ((P j v z).card * m) * (q / g) := by dsimp [T]; ring
          _ ≤ (22 * K * Q * g) * (q / g) :=
            mul_le_mul_of_nonneg_right (hP j v z) (by positivity)
          _ = _ := by field_simp <;> ring
      have hbudget := Submission.Obl.k4_general_parent_projected_layers.weighted_projected_support_budget
        V I G w T (chi := χ) (g := g) (q := Q) hχ.le hg.le hQ.le (by positivity : 0 ≤ 10 * K)
        (by positivity : 0 ≤ 180 * K ^ 2) (by positivity : 0 ≤ 22 * K * q / Q)
        (fun v _ => hw v) hwsum (fun v _ => hI v) (fun v _ z _ => hG v z)
        (fun v _ z _ γ _ => harea v z γ)
      calc
        _ = ∑ v ∈ V, ∑ z ∈ I v, ∑ γ ∈ G v z, (χ * g * w v) * T v z γ := by
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro z hz
          apply Finset.sum_congr rfl
          intro γ hγ
          simp only [Finset.sum_const, nsmul_eq_mul, T]
          field_simp
        _ ≤ (10 * K) * (180 * K ^ 2) * (22 * K * q / Q) * Q ^ 3 * g := hbudget
        _ = _ := by field_simp <;> ring
    have himage : (∑ c ∈ S, q * χ * m * w (c 1)) ≤
        ∑ i ∈ D, q * χ * m * w (decode i 1) :=
      Finset.sum_image_le_of_nonneg (fun c hc => mul_nonneg (by positivity) (hw _))
    calc
      _ ≤ ∑ i ∈ D, q * χ * m * w (decode i 1) := himage
      _ = ∑ j ∈ J, ∑ v ∈ V, ∑ z ∈ I v, ∑ γ ∈ G v z, ∑ _p ∈ P j v z,
          q * χ * m * w v := by
            simp only [Index, D, Finset.sum_sigma, decode, Matrix.cons_val_one, Matrix.cons_val_zero]
      _ ≤ ∑ _j ∈ J, 39600 * K ^ 4 * q * Q ^ 2 * g := Finset.sum_le_sum fun j _ => hper j
      _ = (39600 * K ^ 4 * Q ^ 2 * g) * ((J.card : ℝ) * q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (39600 * K ^ 4 * Q ^ 2 * g) * (6 * Q) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = _ := by ring
  · intro j hj v hv z hz γ hγ p hp
    apply Finset.mem_image.mpr
    refine ⟨⟨j, ⟨v, ⟨z, ⟨γ, p⟩⟩⟩⟩, ?_, rfl⟩
    simpa only [Index, D, Finset.mem_sigma] using And.intro hj (And.intro hv (And.intro hz (And.intro hγ hp)))

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
