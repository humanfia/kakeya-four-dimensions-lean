-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.ProjectedSlicing; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.ProjectedLayers
import Submission.Obl.k4_general_compared_layers_velocity_lists.SlicedWitnesses

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def domainCode (k : ℕ) (h g b : ℝ) (ω : α × ℝ) : ℤ × ℤ × ℤ :=
  movingDomainCode h g b (p.b k ω.1 1) (p.b k ω.1 4) ω.2

theorem measurable_domainCode (hbase : p.Basic) (k : ℕ) (h g b : ℝ) :
    Measurable (p.domainCode k h g b) := by
  have hb : Measurable (p.b k) := (hbase k).1
  unfold domainCode movingDomainCode
  fun_prop

end Parent

namespace ProjectedLayer

variable {α C : Type} [MeasurableSpace α]

abbrev FamilyIndex (layers : C → ProjectedLayer α) := Σ c, Fin (layers c).count

def familyEvent (layers : C → ProjectedLayer α) (i : FamilyIndex layers) : Set (α × ℝ) :=
  (layers i.1).C i.2 ×ˢ Icc (0 : ℝ) 1

def familyReference (layers : C → ProjectedLayer α) (p : Parent α) (k : ℕ)
    (depth : C → ℝ) (m h b : ℝ) (i : FamilyIndex layers) : ℝ≥0∞ :=
  ENNReal.ofReal (h * b) * (layers i.1).unscaledWeight p k (depth i.1) m i.2

/-- Prepare all the actual projected colors on common domains and under
one restriction. Every retained color still covers the final law, and all
stored marginal witnesses use the original weights. -/
theorem prepare_common_slices [Fintype C]
    (layers : C → ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {H m h g b : ℝ} (depth : C → ℝ)
    (hL : ∀ c, (layers c).Valid p k (depth c) m H)
    (hH : 1 ≤ H) (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b)
    (hbβ : ∀ c, b ≤ (layers c).β) (hβg : ∀ c, (layers c).β ≤ g)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k) (hcover : ∀ c, (layers c).Covers σ)
    (δ : ℝ≥0∞) :
    ∃ (menus : FamilyIndex layers → Finset (ℤ × ℤ × ℤ))
      (θ : Measure (α × ℝ)) (S : Finset (SliceIndex menus)),
      θ ≤ σ ∧
      σ univ ≤ θ univ + δ * ((Fintype.card C : ℝ≥0∞) * ENNReal.ofReal (240 * H ^ 3)) ∧
      (∀ e ∈ S, δ * familyReference layers p k depth m h b e.1 ≤
        θ (sliceEvent menus (familyEvent layers) (p.domainCode k h g b) e)) ∧
      (∀ c, ∀ᵐ ω ∂θ, ∃ e ∈ S, e.1.1 = c ∧
        ω ∈ sliceEvent menus (familyEvent layers) (p.domainCode k h g b) e) := by
  classical
  choose D hD hcost using fun c =>
    (layers c).domain_menus p (hL c) hH hh hh1 hb (hbβ c) (hβg c)
  let menus (i : FamilyIndex layers) := D i.1 i.2
  have hbudget : (∑ i : FamilyIndex layers, ((menus i).card : ℝ≥0∞) *
      familyReference layers p k depth m h b i) ≤
      (Fintype.card C : ℝ≥0∞) * ENNReal.ofReal (240 * H ^ 3) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ _c : C, ENNReal.ofReal (240 * H ^ 3) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hcost c
      _ = _ := by simp [nsmul_eq_mul]
  have hE (i : FamilyIndex layers) : MeasurableSet (familyEvent layers i) :=
    ((hL i.1).2.2.2.1 i.2).prod measurableSet_Icc
  have hb₀ := hbase k
  rcases hb₀ with ⟨hbmeas, hν, hπ, hμdom, hρle, hunit, hmass, hP, hbclip, hnative⟩
  have hunitμ : ∀ᵐ ω ∂p.μ k, ω.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    have heq : {ω : α × ℝ | ω.2 ∉ Icc (0 : ℝ) 1} = (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
      ext ω
      simp
    rw [heq]
    exact hunit
  have hunitσ : ∀ᵐ ω ∂σ, ω.2 ∈ Icc (0 : ℝ) 1 :=
    hunitμ.filter_mono (ae_mono (hσ.trans hρle))
  obtain ⟨θ, S, hθ, hθmass, hfloor, hretained⟩ := exists_stored_sliced_witnesses
    σ menus (familyEvent layers) hE (p.domainCode k h g b)
    (p.measurable_domainCode hbase k h g b) (familyReference layers p k depth m h b) δ
    (fun c i => i.1 = c) (by
      intro c
      filter_upwards [hcover c, hunitσ] with ω hω ht
      obtain ⟨i, hi⟩ := hω
      exact ⟨⟨c, i⟩, rfl, hi, ht⟩)
    (by
      intro i ω hω
      exact hD i.1 i.2 ω.1 hω.1 ω.2 hω.2)
  refine ⟨menus, θ, S, hθ, ?_, hfloor, hretained⟩
  exact hθmass.trans (add_le_add le_rfl (mul_le_mul_right hbudget δ))

end ProjectedLayer
end
end Submission.Obl.k4_general_compared_layers_velocity_lists
