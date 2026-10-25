/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/CodedFamilies.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.ChartUnions
import Submission.Lib.K4XInterface.Outputs
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

/-!
Merge disjoint priority pieces having one observable code. The output chart
records the code rather than the identity of the candidate that supplied it.
The selected incidence mass is summed in the unchanged original measures.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open Submission.Lib.K4XInterface

noncomputable section

def codedUnion {X ι β : Type*} (code : ι → β) (A : ι → Set X) (b : β) : Set X :=
  {x | ∃ i, code i = b ∧ x ∈ A i}

theorem codedUnion_measurable {X ι β : Type*} [MeasurableSpace X] [Fintype ι]
    (code : ι → β) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (b : β) :
    MeasurableSet (codedUnion code A b) := by
  classical
  have heq : codedUnion code A b = ⋃ i, if code i = b then A i else ∅ := by
    ext x
    simp [codedUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun i => by split_ifs <;> simp_all

/-- Grouping a nonempty fiber of a finite code map preserves the chart's
geometry and pays only a fixed polynomial format cost. -/
theorem gchart_codedUnion {n M Mc D T : ℕ} {Nk κ j r Bv : ℝ}
    {β : Type*} (code : Fin n → β) (b : β)
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ}
    (A : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hNk : 1 ≤ Nk) (hcount : (n : ℝ) ≤ Nk ^ Mc)
    (hused : ∃ i, code i = b)
    (hchart : ∀ i, code i = b → gchart Nk M D κ T j r Bv Ev c u Q R (A i) (F i) True)
    {ex : Prop} (hex : ex) :
    gchart Nk (M + Mc) D κ T j r Bv Ev c u Q R
      (codedUnion code A b) (codedUnion code F b) ex := by
  classical
  let I := {i : Fin n // code i = b}
  let e := Fintype.equivFin I
  have hn : 0 < Fintype.card I := by
    obtain ⟨i, hi⟩ := hused
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hcard : Fintype.card I ≤ n := by
    simpa using Fintype.card_le_of_injective (fun i : I => i.val) Subtype.val_injective
  have hcount' : (Fintype.card I : ℝ) ≤ Nk ^ Mc :=
    (show (Fintype.card I : ℝ) ≤ (n : ℝ) by exact_mod_cast hcard).trans hcount
  have hAeq : (⋃ i : Fin (Fintype.card I), A (e.symm i).val) = codedUnion code A b := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨(e.symm i).val, (e.symm i).property, hi⟩
    · rintro ⟨i, hi, hx⟩
      apply mem_iUnion.mpr
      refine ⟨e ⟨i, hi⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hx
  have hFeq : (⋃ i : Fin (Fintype.card I), F (e.symm i).val) = codedUnion code F b := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨(e.symm i).val, (e.symm i).property, hi⟩
    · rintro ⟨i, hi, hx⟩
      apply mem_iUnion.mpr
      refine ⟨e ⟨i, hi⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hx
  have hout := gchart_iUnion_fin (fun i => A (e.symm i).val) (fun i => F (e.symm i).val)
    hn hNk hcount' (fun i => hchart _ (e.symm i).property) hex
  rwa [hAeq, hFeq] at hout

/-- Merging codes preserves the complete weighted incidence mass whenever
the original pieces of each one code are disjoint. -/
theorem codedUnion_weighted_mass {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype β] (μ : β → Measure X) (w : β → ENNReal)
    (code : ι → β) (F : ι → Set X) (hF : ∀ i, MeasurableSet (F i))
    (hdisj : ∀ i i', i ≠ i' → code i = code i' → Disjoint (F i) (F i')) :
    (∑ b, w b * μ b (codedUnion code F b)) = ∑ i, w (code i) * μ (code i) (F i) := by
  classical
  simpa only [codedUnion, true_and, ite_true] using
    k4_quadratic_finite_greedy_cover.weighted_assignment_union μ w (fun _ : ι => True)
      code F (fun i _ => hF i) (fun i i' _ _ hne hcode => hdisj i i' hne hcode)

/-- A coded strip family gives the original width-improvement output. Only
the observable code is listed; merging its priority pieces preserves all
of their original incidence mass and a fixed polynomial format. -/
theorem xOutput_of_coded_strips
    {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : (k : ℕ) → Fin (W k) → ℝ} {N : ℕ → ℝ}
    {L Δ κ₁ τ : ℝ} {m M Mc D k i : ℕ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {n : ℕ} {β : Type} [Fintype β]
    (code : Fin n → β) (hused : Function.Surjective code)
    (γ : β → Fin (W k)) (j : β → Fin (2 ^ T i))
    (c u : β → EuclideanSpace ℝ (Fin 2)) (Q : β → Matrix (Fin 2) (Fin 2) ℝ)
    (R : β → MvPolynomial (Fin 4) ℝ)
    (A : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset β)
    (hN : 1 ≤ N k) (hi : i < m) (hdepth : r i + Δ * L ≤ L)
    (hcount : (n : ℝ) ≤ N k ^ Mc)
    (hwidth : ∀ b, |(Q b).det| * (4 : ℝ) ^ T i ≤ N k ^ (-(nw i + Δ * L)))
    (hdisj : ∀ a a', a ≠ a' → γ (code a) = γ (code a') →
      j (code a) = j (code a') → Disjoint (A a) (A a'))
    (hlist : ∀ w o, ((lst w o).card : ℝ) ≤ N k ^ τ)
    (hchart : ∀ a, gchart (N k) M D (N k ^ τ) (T i) ((j (code a) : ℕ) : ℝ)
      (r i) (B k (γ (code a))) (E k (γ (code a))) (c (code a)) (u (code a))
      (Q (code a)) (R (code a)) (A a) (F a) True)
    (hknown : ∀ a, ∀ p ∈ F a,
      code a ∈ lst (γ (code a)) (gobs (B k (γ (code a))) (gδ (N k) L) p))
    (hmass : ENNReal.ofReal (N k ^ (-τ)) ≤ ∑ a,
      ENNReal.ofReal (ω k (γ (code a))) * ((ν k (γ (code a))).prod volume) (F a)) :
    XOutput W ω ν E B N L Δ κ₁ m r T nw (M + Mc) D τ k := by
  classical
  have hcard : Fintype.card β ≤ n := by
    simpa using Fintype.card_le_of_surjective code hused
  have hcard' : (Fintype.card β : ℝ) ≤ N k ^ (M + Mc) := by
    apply (show (Fintype.card β : ℝ) ≤ (n : ℝ) by exact_mod_cast hcard).trans
    exact hcount.trans (pow_le_pow_right₀ hN (by omega))
  have hFA (a : Fin n) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) (hp : p ∈ F a) : p.1 ∈ A a :=
    ((hchart a).2.2.2.2.2.2.2.2.2.2.1 p hp).2.1
  have hFm (a : Fin n) : MeasurableSet (F a) := (hchart a).2.2.2.2.2.2.2.1
  have hFdisj (a a' : Fin n) (hne : a ≠ a') (hc : code a = code a') :
      Disjoint (F a) (F a') := by
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact Set.disjoint_left.mp
      (hdisj a a' hne (by rw [hc]) (by rw [hc])) (hFA a p hp) (hFA a' p hp')
  apply xOutput_of_family (r i) (T i) γ j c u Q R
    (codedUnion code A) (codedUnion code F) hdepth
    (Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl, hwidth⟩⟩) hcard'
  · intro b b' hne hγ hj
    apply Set.disjoint_left.mpr
    rintro l ⟨a, hca, ha⟩ ⟨a', hca', ha'⟩
    have haa : a ≠ a' := by
      intro heq
      subst a'
      exact hne (hca.symm.trans hca')
    exact Set.disjoint_left.mp
      (hdisj a a' haa (by simpa only [hca, hca'] using hγ)
        (by simpa only [hca, hca'] using hj)) ha ha'
  · intro w o
    apply (show ((Finset.univ.filter (fun b => γ b = w ∧
      ∃ p ∈ codedUnion code F b, gobs (B k w) (gδ (N k) L) p = o)).card : ℝ) ≤
        ((lst w o).card : ℝ) from ?_).trans (hlist w o)
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun b => γ b = w ∧
      ∃ p ∈ codedUnion code F b, gobs (B k w) (gδ (N k) L) p = o) ⊆ lst w o from by
        intro b hb
        obtain ⟨hγ, p, ⟨a, hca, hp⟩, hpo⟩ := (Finset.mem_filter.mp hb).2
        have h := hknown a p hp
        rwa [hca, hγ, hpo] at h)
  · intro b
    apply gchart_codedUnion code b A F hN hcount (hused b)
      (fun a ha => by simpa only [ha] using hchart a) trivial
  · have heq := codedUnion_weighted_mass
      (fun b => (ν k (γ b)).prod volume) (fun b => ENNReal.ofReal (ω k (γ b)))
      code F hFm hFdisj
    exact hmass.trans_eq heq.symm

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
