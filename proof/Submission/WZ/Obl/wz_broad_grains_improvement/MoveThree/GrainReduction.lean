-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainReduction.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainStability
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainBounds
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- The stable-selection part of Move 3: either the same-scale terminal state
is obtained, or a power-sized fraction of grain mass has a large coefficient
which survives every deletion of at most half its indices. -/
theorem stable_grain_reduction {ε ζ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (ω h ρ a c g : ℝ) (n N L : ℕ) (x v : Fin n → V)
        (Y : Fin n → Set V) (S : Finset (Fin n)) (Z : Fin n → Set V)
        (y w : Fin N → V) (f : Fin n → Fin N) (z : Fin L → V)
        (e : Fin L → V ≃ₗᵢ[ℝ] V) (Hg : Fin L → Set V)
        (γ : Fin L → Fin N) (m : ℝ),
      h ≤ ε / 4 → A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      C δ h n x v Y S Z ρ N y w f True →
      δ ^ (1 - ω / 100) ≤ ρ → Broad ω ζ δ h ρ n N v S Z f →
      GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m →
      δ ^ ζ * (ρ / δ) * N / n ≤ c → ρ ≤ δ ^ (ω / 100) →
      J ω ζ δ ε ρ c n x v Y 3 ∨
      ∃ Q : Finset (Fin L), Q.Nonempty ∧
        O (δ ^ (ε / 4 + ε / 80)) * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j) ∧
        δ ^ (-ζ) < grainCoefficient a ρ c z e Q ∧
        (∀ i ∈ Q, ∀ j ∈ Q,
          (μ (Hg i)).toReal ≤ δ ^ (-(ε / 80)) * (μ (Hg j)).toReal) ∧
        (∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
          grainCoefficient a ρ c z e Q ≤ 2 ^ p * grainCoefficient a ρ c z e R) := by
  obtain ⟨p, ds, hp, hds, Hs⟩ := stable_grain_selection (by positivity : 0 < ε / 4)
  obtain ⟨dm, hdm, Hm⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (by positivity : 0 < ε / 4) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨dc, hdc, Hc⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 64)
  refine ⟨p, min ds (min dm dc), hp, lt_min hds (lt_min hdm hdc), ?_⟩
  intro δ hδ hδd ω h ρ a c g n N L x v Y S Z y w f z e Hg γ m hh hA hC hρlow hB hG hlen hρup
  have hδds := hδd.trans (min_le_left _ _)
  have hδdm := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδdc := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hhalf, Hδ⟩ := Hs δ hδ hδds
  have hδ1 : δ ≤ 1 := by linarith
  have hquarter : h ≤ 1 / 4 := by linarith
  have hL : 0 < L := grain_card_pos hδ hA hC hG
  have hcard : (L : ℝ) ≤ δ ^ (-(6 : ℝ)) := by
    have hconst : 64 * δ ^ (1 / 2 : ℝ) ≤ 1 := by linarith [Hc δ hδ hδdc]
    calc
      _ ≤ 64 * δ ^ (-(2 * h + 5)) := grain_card_bound hδ hA hC hG
      _ ≤ 64 * δ ^ (-(11 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = (64 * δ ^ (1 / 2 : ℝ)) * δ ^ (-(6 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        norm_num
      _ ≤ 1 * δ ^ (-(6 : ℝ)) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hδ.le _)
      _ = _ := one_mul _
  obtain ⟨Q, hQ, hretain, hbal, hstable⟩ :=
    Hδ h ρ a c 0 g n N L x v S Z y w f z e Hg γ m (by linarith) hL hcard hG
  have hexp : ε / 4 / 20 = ε / 80 := by ring
  rw [hexp] at hretain hbal
  have hbudgetR : δ ^ ε ≤ (δ ^ (ε / 4 + ε / 80) / 2) * δ ^ h := by
    calc
      _ ≤ δ ^ (h + (ε / 4 + ε / 80) + ε / 4) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ε / 4) * (δ ^ (ε / 4 + ε / 80) * δ ^ h) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ (1 / 2) * (δ ^ (ε / 4 + ε / 80) * δ ^ h) :=
        mul_le_mul_of_nonneg_right (Hm δ hδ hδdm) (by positivity)
      _ = _ := by ring
  have hbudget : O (δ ^ ε) ≤ O (δ ^ (ε / 4 + ε / 80) / 2) * O (δ ^ h) := by
    exact (ENNReal.ofReal_le_ofReal hbudgetR).trans_eq (ENNReal.ofReal_mul (by positivity))
  by_cases hsmall : grainCoefficient a ρ c z e Q ≤ δ ^ (-ζ)
  · exact Or.inl (stage_three_of_small_grainCoefficient hδ hδ1 (by linarith)
      (Real.rpow_nonneg hδ.le _) hC hρlow hB hG hlen hρup Q hsmall hretain hbudget)
  · exact Or.inr ⟨Q, hQ, hretain, lt_of_not_ge hsmall, hbal, hstable⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
