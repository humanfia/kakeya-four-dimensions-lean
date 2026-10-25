import Mathlib

/-!
# From a finite relation and a finite cover to the frozen conclusion of o041

`conclusion_of_finset` turns a finite set `H ⊆ A ×ˢ B` of pairs and a finite set `Z` of centres
covering the projections `a + t * b` of `H` into the form of the conclusion of
`Submission.k4_oss_finite_energy_relation`: a relation `R : A → B → Prop` with its `Set.ncard`, and
a cover indexed by `Fin m`.
-/

namespace Submission.Obl.k4_oss_finite_energy_relation

theorem conclusion_of_finset {δ τ t : ℝ} {A B : Finset ℝ} (H : Finset (ℝ × ℝ)) (Z : Finset ℝ)
    (hHsub : H ⊆ A ×ˢ B)
    (hHcard : (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤ (H.card : ℝ))
    (hZcard : (Z.card : ℝ) ≤ (10000 / τ) * (B.card : ℝ))
    (hcov : ∀ p ∈ H, ∃ z ∈ Z, dist (p.1 + t * p.2) z ≤ δ) :
    ∃ R : A → B → Prop, (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤
        (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧
      ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) ≤ (10000 / τ) * (B.card : ℝ) ∧
        ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ := by
  classical
  refine ⟨fun a b => ((a : ℝ), (b : ℝ)) ∈ H, ?_, Z.card, fun i => (Z.equivFin.symm i : ℝ),
    hZcard, ?_⟩
  · have hinj : Function.Injective (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ))) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    have himage : (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ))) ''
        {p : A × B | ((p.1 : ℝ), (p.2 : ℝ)) ∈ H} = (H : Set (ℝ × ℝ)) := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hx
        have hx' := Finset.mem_product.mp (hHsub hx)
        exact ⟨(⟨x.1, hx'.1⟩, ⟨x.2, hx'.2⟩), hx, rfl⟩
    have hncard : Set.ncard {p : A × B | ((p.1 : ℝ), (p.2 : ℝ)) ∈ H} = H.card := by
      rw [← Set.ncard_image_of_injective _ hinj, himage, Set.ncard_coe_finset]
    rw [hncard]
    exact hHcard
  · intro a b hab
    obtain ⟨z, hz, hdist⟩ := hcov _ hab
    exact ⟨Z.equivFin ⟨z, hz⟩, by simpa using hdist⟩

end Submission.Obl.k4_oss_finite_energy_relation
