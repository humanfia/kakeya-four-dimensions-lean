-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.WeakUnitProductGrowth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanIteration
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanExponent
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Product sums grow relative to cardinality under any fixed positive
Frostman exponent and any entropy upper exponent bounded away from one.
This normalized version retains one as an element. -/
theorem weak_unit_product_growth (ε β : ℝ) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ τ α C : ℝ, 0 < δ → δ ≤ δ₀ → β ≤ τ → α ≤ 1 - ε →
        1 ≤ C → C ≤ δ ^ (-η) →
        ∀ A : Finset ℝ, (1 : ℝ) ∈ A → (∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1) →
          RealFiniteFrostman δ C τ A →
          (∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) →
          (A.card : ℝ) ≤ δ ^ (-α - η) →
          CoverLower δ (↑(A * A + A * A) : Set ℝ) (δ ^ (-η) * (A.card : ℝ)) := by
  classical
  let e := min ε (1 / 4)
  let b := min β (1 / 4)
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 4 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hb : 0 < b := lt_min hβ (by norm_num)
  have hb1 : b ≤ 1 / 4 := min_le_right _ _
  have hbβ : b ≤ β := min_le_left _ _
  obtain ⟨g, hg, hiter⟩ := product_frostman_iteration (e / 2) b (by positivity) hb
  have hex : ∃ N : ℕ, 1 - e / 2 < b + (N : ℝ) * g := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 - e / 2 - b) / g)
    have hh := (div_lt_iff₀ hg).mp hN
    exact ⟨N, by linarith⟩
  let N := Nat.find hex
  have hNlow : 1 - e / 2 < b + (N : ℝ) * g := Nat.find_spec hex
  have hNhigh : b + (N : ℝ) * g ≤ 1 - e / 2 + g := by
    by_cases hN0 : N = 0
    · simp only [hN0, Nat.cast_zero, zero_mul, add_zero]
      linarith
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0
      have hbefore : ¬ (1 - e / 2 < b + (k : ℝ) * g) := Nat.find_min hex (by change k < N; omega)
      have hbefore' : b + (k : ℝ) * g ≤ 1 - e / 2 := le_of_not_gt hbefore
      rw [hk]
      push_cast
      nlinarith
  obtain ⟨ηI, dI, hηI, hdI, hdI1, hfinal⟩ := hiter N hNhigh (e / 8) (by positivity)
  let η := min ηI (e / 8)
  have hη : 0 < η := lt_min hηI (by positivity)
  have hηI' : η ≤ ηI := min_le_left _ _
  have hηe : η ≤ e / 8 := min_le_right _ _
  refine ⟨η, min dI (1 / 2), hη, lt_min hdI (by norm_num),
    (min_le_left _ _).trans hdI1, ?_⟩
  intro δ τ α C hδ hδs hτ hα hC hCb A hA1 hAb hAF hsep hAc
  have hδ1 : δ ≤ 1 := (hδs.trans (min_le_left _ _)).trans hdI1
  have hδlt : δ < 1 := by have hh := hδs.trans (min_le_right _ _); linarith
  have herr : δ ^ (-η) ≤ δ ^ (-ηI) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hAFb := hAF.lower_exponent hδ hC hb.le (hbβ.trans hτ)
  by_contra hbad
  unfold CoverLower at hbad
  push_neg at hbad
  obtain ⟨m, cc, hc, hm⟩ := hbad
  have hsmall : RealCoverBound δ (A * A + A * A) (δ ^ (-ηI) * (A.card : ℝ)) :=
    ⟨m, cc, hc, hm.le.trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _))⟩
  have hFend := hfinal δ hδ (hδs.trans (min_le_left _ _)) A hA1 hAb
    (hAFb.weaken hδ (hCb.trans herr)) hsep hsmall
  have hlower := hFend.card_power_lower hδ (show A.Nonempty from ⟨1, hA1⟩) le_rfl
  have hstrict : δ ^ (-α - η) < δ ^ (e / 8 - (b + (N : ℝ) * g)) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by linarith)
  exact (not_le_of_gt hstrict) (hlower.trans hAc)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
