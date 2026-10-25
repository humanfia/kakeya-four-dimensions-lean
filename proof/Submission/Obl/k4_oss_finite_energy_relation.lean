import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_finite_energy_relation.Energy
import Submission.Obl.k4_oss_finite_energy_relation.CellCover
import Submission.Obl.k4_oss_finite_energy_relation.Wrapper
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_finite_energy_relation`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_finite_energy_relation`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_finite_energy_relation/`
belong to this obligation.
-/

theorem Submission.k4_oss_finite_energy_relation : ∀ δ τ : ℝ, 0 < δ → 0 < τ → τ ≤ 1 → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → ∀ t : ℝ, t ∈ Set.Icc (1 / 4 : ℝ) 1 → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ) → ∃ R : A → B → Prop, (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤ (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) ≤ (10000 / τ) * (B.card : ℝ) ∧ ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ := by
  classical
  intro δ τ hδ hτ hτ₁ A B hA hB t ht hAsep hBsep henergy
  obtain ⟨H, hHsub, hHcard, hpopular⟩ :=
    Submission.Obl.k4_oss_finite_energy_relation.exists_popular_projection_points
      hδ hτ ht.1 A B hA hBsep henergy
  let Z := H.image (fun p : ℝ × ℝ => δ * (⌊(p.1 + t * p.2) / δ⌋ : ℝ))
  have hcovercard := Submission.Obl.k4_oss_finite_energy_relation.cell_cover_card
    hδ (fun p : ℝ × ℝ => p.1 + t * p.2) (A.product B) H hpopular
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBnonneg : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hZcard : (Z.card : ℝ) ≤ (10000 / τ) * (B.card : ℝ) := by
    change (Z.card : ℝ) * (τ * (A.card : ℝ) / 2) ≤ 36 * ((A.product B).card : ℝ)
      at hcovercard
    simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul] at hcovercard
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hτ).mpr
    apply (mul_le_mul_iff_left₀ hApos).mp
    nlinarith only [hcovercard, mul_nonneg hApos.le hBnonneg]
  apply Submission.Obl.k4_oss_finite_energy_relation.conclusion_of_finset H Z hHsub
  · calc
      (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤
          (τ / 260) * (A.card : ℝ) * (B.card : ℝ) := by gcongr; norm_num
      _ ≤ (H.card : ℝ) := hHcard
  · exact hZcard
  · intro p hp
    refine ⟨δ * (⌊(p.1 + t * p.2) / δ⌋ : ℝ), Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    exact Submission.Obl.k4_oss_finite_energy_relation.dist_cell_le hδ _
