-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorFrozen.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorEps

/-!
# WZ Proposition 4.6 for unit `ρ`-tubes: a statement ready to be frozen, and its proof

`factorFrozen` mentions only Mathlib and `ChallengeDeps` names (it elaborates in a file importing
just those, with `autoImplicit` off) and is short enough to be a child's frozen type. It binds the
tube `T d p q = thickening d (segment p (p+q))` and the box
`P a b c z e = {p | |e(p-z)₀| ≤ a/2 ∧ |e(p-z)₁| ≤ b/2 ∧ |e(p-z)₂| ≤ c/2}` (the `P` of the proposed
split) by defining equations. `factor_frozen` proves it.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- WZ Proposition 4.6 (factoring convex sets) for `N` unit `ρ`-tubes in `ball 0 R`. -/
def factorFrozen : Prop :=
  ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ P, P = (fun (a b c : ℝ) (z : LeanEval.Analysis.WangZahlKakeya.Space) (e : LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) => {p : LeanEval.Analysis.WangZahlKakeya.Space | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}) → ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space), 0 < N → (∀ k, ‖w k‖ = 1) → (∀ k, T ρ (y k) (w k) ⊆ Metric.ball 0 R) → ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → LeanEval.Analysis.WangZahlKakeya.Space) (e : Fin L → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space), (N : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε * U.card ∧ 0 < m ∧ ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 * R ∧ (∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) ∧ (∀ i, m * (a * b * (2 * R)) ≤ C * ((N : ℝ) / ρ) ^ ε * (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} * ρ ^ 2)) ∧ (∀ k ∈ U, 1 ≤ Set.ncard {i | T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} ∧ (Set.ncard {i | T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε) ∧ (∀ V, Convex ℝ V → ENNReal.ofReal (Set.ncard {i | P a b (2 * R) (z i) (e i) ⊆ V} * (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε) * MeasureTheory.volume V) ∧ ∀ i V, Convex ℝ V → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i) ∩ V} * (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε * Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)}) * MeasureTheory.volume V

theorem ncard_sub {N : ℕ} {ρ : ℝ} {y w : Fin N → Space} (U : Finset (Fin N)) (W : Set Space) :
    Set.ncard {k | k ∈ U ∧ thickening ρ (segment ℝ (y k) (y k + w k)) ⊆ W} =
      (sub ρ y w U W).card := by
  rw [← Set.ncard_coe_finset, sub, Finset.coe_filter]
  rfl

theorem ncard_univ_filter {L : ℕ} (p : Fin L → Prop) :
    Set.ncard {i | p i} = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

theorem factor_frozen : factorFrozen := by
  intro T hT P hP ε hε R hR
  subst hT hP
  obtain ⟨C, hC1, hC⟩ := Kc_le ε hε R hR
  refine ⟨C, hC1, fun ρ hρ hρ1 N y w hN hw hball => ?_⟩
  have hF : Fam R ρ y w := ⟨hρ, hρ1, hw, hball⟩
  have hK := hC N hN ρ hρ hρ1
  have hR0 : 0 < R := by linarith
  have hKpos := Kc_pos hR0 N ρ
  obtain ⟨U, m, a, b, L, z, e, h1, hm, ha1, hab, hb2, hKT, h45, hcov, hboxKT, hfrost⟩ :=
    hF.factor hR hN
  refine ⟨U, m, a, b, L, z, e, ?_, hm, ha1, hab, hb2, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1.trans (by gcongr)
  · intro W hW
    rw [ncard_sub U W]
    exact hKT W hW
  · intro i
    rw [ncard_sub U _]
    show m * (a * b * (2 * R)) ≤
      C * ((N : ℝ) / ρ) ^ ε * (((sub ρ y w U (box a b (2 * R) (z i) (e i))).card : ℝ) * ρ ^ 2)
    refine (h45 i).trans ?_
    gcongr
  · intro k hk
    rw [ncard_univ_filter]
    exact ⟨(hcov k hk).1, (hcov k hk).2.trans hK⟩
  · intro V hV
    rw [ncard_univ_filter]
    show ENNReal.ofReal (((Finset.univ.filter fun i => box a b (2 * R) (z i) (e i) ⊆ V).card : ℝ) *
      (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε) * volume V
    refine (hboxKT V hV).trans ?_
    gcongr
  · intro i V hV
    rw [ncard_sub U _, ncard_sub U _]
    show ENNReal.ofReal (((sub ρ y w U (box a b (2 * R) (z i) (e i) ∩ V)).card : ℝ) *
      (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε *
        (sub ρ y w U (box a b (2 * R) (z i) (e i))).card) * volume V
    refine (hfrost i V hV).trans ?_
    gcongr

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
