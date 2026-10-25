/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/FiniteCode.lean. -/
import Mathlib

open MeasureTheory Set

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- Encode a finite-range measurable joint record on a nonempty support using
`Fin n`. Every decoded value still comes from the original support. -/
theorem exists_finite_code_on {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A]
    (S : Set Ω) (hS : MeasurableSet S) (hSne : S.Nonempty)
    (G : Ω → A) (hG : Measurable G) (hfin : (G '' S).Finite) :
    ∃ n : ℕ, 0 < n ∧ ∃ (X : Ω → Fin n) (decode : Fin n → A),
      Measurable X ∧ (∀ x ∈ S, decode (X x) = G x) ∧
      ∀ i, decode i ∈ G '' S := by
  classical
  obtain ⟨x₀, hx₀⟩ := hSne
  let I : Set A := G '' S
  letI : Fintype I := hfin.fintype
  haveI : Nonempty I := ⟨⟨G x₀, ⟨x₀, hx₀, rfl⟩⟩⟩
  let g₀ : Ω → A := S.piecewise G (fun _ => G x₀)
  have hg₀ : Measurable g₀ := hG.piecewise hS measurable_const
  have hgin : ∀ x, g₀ x ∈ I := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨x, hx, by simp [g₀, hx]⟩
    · exact ⟨x₀, hx₀, by simp [g₀, hx]⟩
  let g : Ω → I := fun x => ⟨g₀ x, hgin x⟩
  have hg : Measurable g := hg₀.subtype_mk
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, Fintype.card_pos, e ∘ g, fun i => (e.symm i).1,
    (measurable_of_countable e).comp hg, ?_, ?_⟩
  · intro x hx
    change (e.symm (e (g x))).1 = G x
    rw [e.symm_apply_apply]
    simp [g, g₀, hx]
  · intro i
    exact (e.symm i).2

/-- A full-mass support of a probability law is automatically nonempty. -/
theorem exists_finite_code_ae {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (G : Ω → A) (hG : Measurable G) (hfin : (G '' S).Finite) :
    ∃ n : ℕ, 0 < n ∧ ∃ (X : Ω → Fin n) (decode : Fin n → A),
      Measurable X ∧ (∀ x ∈ S, decode (X x) = G x) ∧
      ∀ i, decode i ∈ G '' S := by
  have hmass : μ S = 1 := by
    simpa [hμS] using measure_add_measure_compl (μ := μ) hS
  exact exists_finite_code_on S hS
    (nonempty_of_measure_ne_zero (by rw [hmass]; exact one_ne_zero)) G hG hfin

/-- A finite family of finite-range records and a finite-range palette have
finite joint range on the retained support. -/
theorem finite_joint_record_range {Ω I : Type*} [Finite I]
    (S : Set Ω) (F : I → Ω → ℕ) (z : Ω → ℕ)
    (hF : ∀ i, (F i '' S).Finite) (hz : (z '' S).Finite) :
    ((fun x => ((fun i => F i x), z x)) '' S).Finite := by
  apply ((Set.Finite.pi hF).prod hz).subset
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨fun i _ => ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- Construct the finite joint code used when applying the palette theorem.
Every finite-code value has a representative in the retained event support,
so identities between original records transfer to all code values. -/
theorem exists_joint_record_code {Ω I : Type*}
    [MeasurableSpace Ω] [Finite I]
    (S : Set Ω) (hS : MeasurableSet S) (hSne : S.Nonempty)
    (F : I → Ω → ℕ) (z : Ω → ℕ)
    (hFm : ∀ i, Measurable (F i)) (hzm : Measurable z)
    (hFfin : ∀ i, (F i '' S).Finite) (hzfin : (z '' S).Finite) :
    ∃ n : ℕ, 0 < n ∧ ∃ (X : Ω → Fin n) (F' : I → Fin n → ℕ) (z' : Fin n → ℕ),
      Measurable X ∧
      (∀ x ∈ S, ∀ i, F' i (X x) = F i x) ∧
      (∀ x ∈ S, z' (X x) = z x) ∧
      ∀ a, ∃ x ∈ S, (∀ i, F' i a = F i x) ∧ z' a = z x := by
  let G : Ω → (I → ℕ) × ℕ := fun x => ((fun i => F i x), z x)
  have hG : Measurable G := (measurable_pi_lambda hFm).prodMk hzm
  obtain ⟨n, hn, X, decode, hX, hdecode, hrepr⟩ := exists_finite_code_on S hS hSne G hG
    (finite_joint_record_range S F z hFfin hzfin)
  refine ⟨n, hn, X, (fun i a => (decode a).1 i), (fun a => (decode a).2), hX,
    ?_, ?_, ?_⟩
  · intro x hx i
    exact congrArg (fun p => p.1 i) (hdecode x hx)
  · intro x hx
    exact congrArg Prod.snd (hdecode x hx)
  · intro a
    obtain ⟨x, hx, heq⟩ := hrepr a
    exact ⟨x, hx, (fun i => congrArg (fun p => p.1 i) heq.symm),
      congrArg Prod.snd heq.symm⟩


end Submission.Obl.k4_matching_cofinal_palette_selection
