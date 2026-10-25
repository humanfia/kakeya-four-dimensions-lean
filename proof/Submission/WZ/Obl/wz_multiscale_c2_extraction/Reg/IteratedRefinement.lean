-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.IteratedRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

/-- Uniform refinements may be iterated at finitely many scales. Error parameters
are chosen backwards, so every output satisfies the next input hypothesis.
Properties obtained at earlier scales persist under further refinement. -/
theorem simultaneous_uniform_refinement {ι P : Type*} {A : P → Type*}
    (refines : ∀ p, A p → A p → Prop)
    (hreflexive : ∀ p a, refines p a a)
    (htransitive : ∀ p a b c, refines p a b → refines p b c → refines p a c)
    (regular : ℝ → ℝ → ∀ p, A p → Prop) (fits : ι → ℝ → ∀ p, A p → Prop)
    (hfits : ∀ i δ p a b, refines p a b → fits i δ p b → fits i δ p a)
    (hstep : ∀ i : ι, ∀ ε : ℝ, 0 < ε →
      ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ p, ∀ a : A p, regular η δ p a →
          ∃ b : A p, refines p b a ∧ regular ε δ p b ∧ fits i δ p b)
    (J : Finset ι) :
    ∀ ε : ℝ, 0 < ε → ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ p, ∀ a : A p, regular η δ p a →
        ∃ b : A p, refines p b a ∧ regular ε δ p b ∧ ∀ i ∈ J, fits i δ p b := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨ε, 1, hε, le_rfl, zero_lt_one, ?_⟩
      intro δ hδ hδ1 p a ha
      exact ⟨a, hreflexive p a, ha, by simp⟩
  | @insert i J hi hJ =>
      intro ε hε
      obtain ⟨η₁, d₁, hη₁, hη₁ε, hd₁, hlast⟩ := hstep i ε hε
      obtain ⟨η₀, d₀, hη₀, hη₀η₁, hd₀, hfirst⟩ := hJ η₁ hη₁
      refine ⟨η₀, min d₀ d₁, hη₀, hη₀η₁.trans hη₁ε, lt_min hd₀ hd₁, ?_⟩
      intro δ hδ hδd p a ha
      obtain ⟨b, hba, hb, hbfits⟩ :=
        hfirst δ hδ (hδd.trans (min_le_left _ _)) p a ha
      obtain ⟨c, hcb, hc, hcfits⟩ :=
        hlast δ hδ (hδd.trans (min_le_right _ _)) p b hb
      refine ⟨c, htransitive p c b a hcb hba, hc, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hcfits
      · exact hfits j δ p c b hcb (hbfits j hj)

/-- The finite iteration can also impose any fixed positive upper bound on the
initial error. This follows by including an error-reduction step before the
geometric refinements, without strengthening any of their conclusions. -/
theorem simultaneous_uniform_refinement_with_error_bound {ι P : Type*} {A : P → Type*}
    (refines : ∀ p, A p → A p → Prop)
    (hreflexive : ∀ p a, refines p a a)
    (htransitive : ∀ p a b c, refines p a b → refines p b c → refines p a c)
    (regular : ℝ → ℝ → ∀ p, A p → Prop) (fits : ι → ℝ → ∀ p, A p → Prop)
    (hregular : ∀ η ε δ p a, η ≤ ε → regular η δ p a → regular ε δ p a)
    (hfits : ∀ i δ p a b, refines p a b → fits i δ p b → fits i δ p a)
    (hstep : ∀ i : ι, ∀ ε : ℝ, 0 < ε →
      ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ p, ∀ a : A p, regular η δ p a →
          ∃ b : A p, refines p b a ∧ regular ε δ p b ∧ fits i δ p b)
    (J : Finset ι) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ η ≤ β ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ p, ∀ a : A p, regular η δ p a →
        ∃ b : A p, refines p b a ∧ regular ε δ p b ∧ ∀ i ∈ J, fits i δ p b := by
  obtain ⟨η, d₀, hη, hηε, hd₀, h⟩ :=
    simultaneous_uniform_refinement refines hreflexive htransitive regular fits hfits hstep J ε hε
  refine ⟨min η β, d₀, lt_min hη hβ, (min_le_left _ _).trans hηε,
    min_le_right _ _, hd₀, ?_⟩
  intro δ hδ hδd p a ha
  exact h δ hδ hδd p a (hregular _ _ _ _ _ (min_le_left _ _) ha)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
