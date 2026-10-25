import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_bad_direction_extraction.Energy
import Submission.Obl.k4_oss_bad_direction_extraction.Extraction
import Submission.Obl.k4_oss_bad_direction_extraction.Numerics
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_bad_direction_extraction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_bad_direction_extraction`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_bad_direction_extraction/`
belong to this obligation.
-/

theorem Submission.k4_oss_bad_direction_extraction : (∀ δ τ : ℝ, 0 < δ → 0 < τ → τ ≤ 1 → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → ∀ t : ℝ, t ∈ Set.Icc (1 / 4 : ℝ) 1 → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ) → ∃ R : A → B → Prop, (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤ (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) ≤ (10000 / τ) * (B.card : ℝ) ∧ ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ) → ∀ b η : ℝ, 0 < b → b ≤ 1 → 0 < η → ∃ θ r : ℝ, 0 < θ ∧ θ ≤ η ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → (B.card : ℝ) ≤ δ ^ (-2 * θ) * (A.card : ℝ) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (b))) → ¬ (MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤ ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))) → ∃ S : Finset ℝ, S.Nonempty ∧ (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x u : ℝ, δ ≤ u → ((S.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-η) * u ^ b * (S.card : ℝ)) ∧ ∀ t ∈ S, ∃ R : A → B → Prop, δ ^ η * (A.card : ℝ) * (B.card : ℝ) ≤ (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) < δ ^ (-η) * (A.card : ℝ) ∧ ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ := by
  classical
  intro H b η hb hb1 hη
  obtain ⟨θ, r, hθ, hθη, hr, hr1, hparameters⟩ :=
    Submission.Obl.k4_oss_bad_direction_extraction.extraction_parameters hb hη
  refine ⟨θ, r, hθ, hθη, hr, hr1, ?_⟩
  intro δ hδ hδr A B hA hB hAsep hBsep hcard ν hprob hν hcap hlarge
  let : MeasureTheory.IsProbabilityMeasure ν := hprob
  obtain ⟨hδ1, hθpow, hsmall, habsorb, hcount, hdensity, hcover⟩ := hparameters δ hδ hδr
  let E : Set ℝ := {t | t ∈ Set.Icc (1 / 4 : ℝ) 1 ∧
    δ ^ θ / 2 * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤
      ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)}
  have hE : MeasurableSet E :=
    Submission.Obl.k4_oss_bad_direction_extraction.measurableSet_bad A B δ _
  have hsupp : E ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1.1], ht.1.2⟩
  have hm : 0 < δ ^ θ / 258 := by positivity
  have hmass : δ ^ θ / 258 ≤ ν.real E := by
    have hh := Submission.Obl.k4_oss_bad_direction_extraction.bad_mass A B hδ
      (Real.rpow_nonneg hδ.le θ) hBsep ν hν hlarge
    change ENNReal.ofReal (δ ^ θ / 258) ≤ ν E at hh
    have hhR := ENNReal.toReal_mono (by finiteness : ν E ≠ ⊤) hh
    simpa only [ENNReal.toReal_ofReal hm.le, MeasureTheory.measureReal_def] using hhR
  have hC : 1 ≤ δ ^ (-θ) := by
    calc
      1 = δ ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ δ ^ (-θ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  obtain ⟨S, hS, hSE, hSF⟩ :=
    Submission.Obl.k4_oss_bad_direction_extraction.finite_frostman_extraction
      hδ hδ1 hb.le hb1 hC (Real.rpow_nonneg hδ.le (-η)) hm
      (Real.rpow_nonneg hδ.le (-(η / 4))) hsmall habsorb hcount ν hcap E hE hsupp hmass
  refine ⟨S, hS, fun t ht => hsupp (hSE t ht), hSF, ?_⟩
  intro t ht
  have htE := hSE t ht
  exact Submission.Obl.k4_oss_bad_direction_extraction.relation_of_large_energy H hδ hδ1 hθ.le
    (by linarith) hcover A B hA hB hAsep hBsep hcard htE.1 htE.2
