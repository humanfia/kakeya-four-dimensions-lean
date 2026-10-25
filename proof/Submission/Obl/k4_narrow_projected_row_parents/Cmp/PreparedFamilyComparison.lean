/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedFamilyComparison.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedEligibleFamilies
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedReferenceBudget
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.FiniteOriginalComparison

/-! The actual eligible prepared families, their reference budget and retained partner lists. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open scoped ENNReal Classical

noncomputable section

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

theorem compare_families [IsFiniteMeasure ζ] (hp : p.Valid) (hcommon : a.Common p)
    (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    {aTable Bcap Fprune Llist ε C Λ : ℝ} (Kchart : NNReal)
    (M : ∀ u, ComparisonMesh (D.law u))
    (signal : α × ℝ → ℝ) (hsignal : Measurable signal)
    (full₁ full₂ : ∀ u, OriginalSheetFamily (D.law u) 4 aTable Kchart (M u).base signal)
    (oldTrue : ∀ u, Fin (full₁ u).n → Fin (a.n k s) × Bool)
    (oldProjected : ∀ u, Fin (full₂ u).n → Fin L.n)
    (hTrue : ∀ u, Function.Injective (oldTrue u))
    (hProjected : ∀ u, Function.Injective (oldProjected u))
    (hsource₁ : ∀ u i z, z ∈ (full₁ u).witness i → z ∈ D.core u ∧
      z.1 ∈ a.B k s (oldTrue u i).1 ∧ z.2 ∈ a.block k s (oldTrue u i).1)
    (hsource₂ : ∀ u i z, z ∈ (full₂ u).witness i → z ∈ D.core u ∧ z.1 ∈ L.C (oldProjected u i))
    (haTable : 0 < aTable) (hBcap : 0 < Bcap) (hFprune : 0 < Fprune)
    (hLlist : 1 ≤ Llist) (hLfloor : 14 * Bcap * Fprune ≤ Llist)
    (hpalette : ∀ u, a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode u) 1} ≠ 0)
    (hresolve : ∀ u, 2 * (Kchart : ℝ) * (M u).diameter ≤ aTable / 2)
    (hvolume : ∀ u, (∑ _j : Fin (M u).n, (M u).vol) ≤ 1)
    (hnative : ∀ u (R : ℝ), aTable ≤ R → ∀ j x,
      D.law u {z | (M u).code z = j ∧ ⌊signal z / R⌋ = x} ≤
        (ENNReal.ofReal (Bcap * ((q * χ * m) * aTable ^ p.d) * (R / aTable) ^ p.d) *
          a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode u) 1}) * (M u).vol)
    (Match : ComparisonEstimate 4 p.d ε C) (hC : 0 ≤ C)
    (hΛ : C * Llist ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ) :
    let Rtotal := (aTable / PreparedModel.width p k s) ^ p.d *
      (475200 * p.K k ^ 5 + 360 * H ^ 4 * p.K k)
    ∃ (ρ : Measure (α × ℝ)) (tru : α × ℝ → Fin (a.n k s) × Bool)
      (lab : α × ℝ → Fin L.n)
      (forward : Fin D.n → Fin (a.n k s) → Finset (Fin L.n))
      (reverse : Fin D.n → Fin L.n → Finset (Fin (a.n k s))),
      Measurable tru ∧ Measurable lab ∧
      (∀ z, tru z = oldTrue (D.code z) ((full₁ (D.code z)).index z)) ∧
      (∀ z, lab z = oldProjected (D.code z) ((full₂ (D.code z)).index z)) ∧
      ρ ≤ ζ ∧ ζ univ ≤ ρ univ + ENNReal.ofReal (Rtotal / Fprune) +
        ENNReal.ofReal (C * (6 * Bcap) * Λ ^ (-ε) * Rtotal) ∧
      (∀ u i, ((forward u i).card : ℝ) ≤ 2 * (Llist * Λ ^ p.d)) ∧
      (∀ u j, ((reverse u j).card : ℝ) ≤ Llist * Λ ^ p.d) ∧
      (∀ᵐ z ∂ρ, z ∈ D.G ∧ z.1 ∈ a.B k s (tru z).1 ∧ z.2 ∈ a.block k s (tru z).1 ∧
        z.1 ∈ L.C (lab z) ∧ lab z ∈ forward (D.code z) (tru z).1 ∧
        (tru z).1 ∈ reverse (D.code z) (lab z)) ∧
      ∀ᵐ z ∂ρ, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
        ‖(full₁ (D.code z)).f ((full₁ (D.code z)).index z) (emb x) -
          (full₂ (D.code z)).f ((full₂ (D.code z)).index z) (emb x)‖ ≤ Λ * aTable := by
  classical
  dsimp only
  choose f₁ trueIdx htrue heligible₁ hsourceNew₁ retain₁ hretain₁ hidx₁ hsame₁ hW₁ hcurrent₁ using
    fun u => D.eligible_true_family u (full₁ u) (oldTrue u) (hTrue u) (hsource₁ u)
  choose f₂ projectedIdx hprojected heligible₂ hsourceNew₂ retain₂ hretain₂ hidx₂ hsame₂ hW₂ hcurrent₂ using
    fun u => D.eligible_projected_family u (full₂ u) (oldProjected u) (hProjected u) (hsource₂ u)
  haveI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
  have hreference := D.reference_bound hp hcommon hq hχ hm haTable
    (fun u => (f₁ u).n) (fun u => (f₂ u).n) trueIdx projectedIdx htrue hprojected heligible₁ heligible₂
  obtain ⟨ρ, forward, reverse, hρ, hmass, hforward, hreverse, hmem, hagreement⟩ :=
    finite_original_comparison_with_agreement ζ D.code D.measurable_code Kchart M signal hsignal
      f₁ f₂ trueIdx projectedIdx htrue hprojected haTable hBcap hFprune hLlist hLfloor
      (fun _ => (q * χ * m) * aTable ^ p.d) (fun _ => by positivity)
      (fun u => a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode u) 1}) hpalette (fun _ => measure_ne_top _ _)
      hresolve hvolume hnative hreference Match hC hΛ hΛ1
  let tru (z : α × ℝ) := oldTrue (D.code z) ((full₁ (D.code z)).index z)
  let lab (z : α × ℝ) := oldProjected (D.code z) ((full₂ (D.code z)).index z)
  have htru : Measurable tru := by
    have h : Measurable (fun z : Fin D.n × (α × ℝ) => oldTrue z.1 ((full₁ z.1).index z.2)) :=
      measurable_from_prod_countable_right fun u =>
        (measurable_of_finite (oldTrue u)).comp (full₁ u).measurable_index
    exact h.comp (D.measurable_code.prodMk measurable_id)
  have hlab : Measurable lab := by
    have h : Measurable (fun z : Fin D.n × (α × ℝ) => oldProjected z.1 ((full₂ z.1).index z.2)) :=
      measurable_from_prod_countable_right fun u =>
        (measurable_of_finite (oldProjected u)).comp (full₂ u).measurable_index
    exact h.comp (D.measurable_code.prodMk measurable_id)
  have hcurrent (u : Fin D.n) : ∀ᵐ z ∂ζ, D.code z = u →
      z ∈ (full₁ u).witness ((full₁ u).index z) ∧ z ∈ (full₂ u).witness ((full₂ u).index z) ∧
      retain₁ u ((f₁ u).index z) = (full₁ u).index z ∧ retain₂ u ((f₂ u).index z) = (full₂ u).index z := by
    have hmeas : MeasurableSet {z | D.code z = u} := D.measurable_code (measurableSet_singleton u)
    apply (ae_restrict_iff' hmeas).mp
    change ∀ᵐ z ∂D.law u, _
    exact (full₁ u).assigned.and ((full₂ u).assigned.and ((hcurrent₁ u).and (hcurrent₂ u)))
  have hall : ∀ᵐ z ∂ζ, ∀ u : Fin D.n, D.code z = u →
      z ∈ (full₁ u).witness ((full₁ u).index z) ∧ z ∈ (full₂ u).witness ((full₂ u).index z) ∧
      retain₁ u ((f₁ u).index z) = (full₁ u).index z ∧ retain₂ u ((f₂ u).index z) = (full₂ u).index z :=
    ae_all_iff.mpr hcurrent
  have hG : ∀ᵐ z ∂ζ, z ∈ D.G := ae_iff.mpr D.full_G
  have hallρ : ∀ᵐ z ∂ρ, ∀ u : Fin D.n, D.code z = u →
      z ∈ (full₁ u).witness ((full₁ u).index z) ∧ z ∈ (full₂ u).witness ((full₂ u).index z) ∧
      retain₁ u ((f₁ u).index z) = (full₁ u).index z ∧ retain₂ u ((f₂ u).index z) = (full₂ u).index z :=
    ae_mono hρ hall
  refine ⟨ρ, tru, lab, forward, reverse, htru, hlab, (fun _ => rfl), (fun _ => rfl),
    hρ, hmass, hforward, hreverse, ?_, ?_⟩
  · filter_upwards [hmem, hallρ, ae_mono hρ hG] with z hz hcur hGz
    obtain ⟨hW₁, hW₂, hret₁, hret₂⟩ := hcur (D.code z) rfl
    have htrue' : trueIdx (D.code z) ((f₁ (D.code z)).index z) = tru z :=
      (hidx₁ _ _).trans (congrArg (oldTrue (D.code z)) hret₁)
    have hprojected' : projectedIdx (D.code z) ((f₂ (D.code z)).index z) = lab z :=
      (hidx₂ _ _).trans (congrArg (oldProjected (D.code z)) hret₂)
    rw [htrue', hprojected'] at hz
    have hsourceT := hsource₁ (D.code z) _ z hW₁
    have hsourceP := hsource₂ (D.code z) _ z hW₂
    exact ⟨hGz, hsourceT.2.1, hsourceT.2.2, hsourceP.2, hz⟩
  · filter_upwards [hagreement, hallρ] with z hz hcur
    obtain ⟨-, -, hret₁, hret₂⟩ := hcur (D.code z) rfl
    intro x hx
    have h := hz x hx
    rw [hsame₁ _ _, hsame₂ _ _, hret₁, hret₂] at h
    exact h

end PreparedDomainData

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
