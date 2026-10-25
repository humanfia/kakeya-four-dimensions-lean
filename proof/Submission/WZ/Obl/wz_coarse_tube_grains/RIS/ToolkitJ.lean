-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ToolkitJ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ToolkitFrozen
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorJ

/-!
# The convex toolkit with the J-ready form of Proposition 4.6

`toolkit2Frozen` (3262 characters, Mathlib-only, checked standalone) is `toolkitFrozen` with its first
conjunct replaced by the J-ready form of WZ Proposition 4.6 for unit `ρ`-tubes in `ball 0 R`
(`Fam.factor_assign`): a sub-collection `U` with `N ≤ K #U`, `m ≥ KT(U)`, congruent boxes
`P a b (2R) (z i) (e i)` (`ρ ≤ a ≤ b ≤ 2R`) and an assignment `g` of the tubes of `U` to boxes
containing them, with `K`-balanced, rich fibres (`m·2Rab ≤ K #fibre ρ²`), each tube in at most `K`
boxes, the boxes Katz–Tao and each fibre Frostman inside its box (all with error `K = C (N/ρ)^ε`).
This is exactly the box data that the flat-prism estimate (`J`/`Jb`) takes.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

theorem ncard_filter_eq {n : ℕ} (U : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    Set.ncard {k | k ∈ U ∧ p k} = (U.filter p).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

theorem Kc_one_le {R : ℝ} (hR : 1 ≤ R) (N : ℕ) (ρ : ℝ) : 1 ≤ Kc R N ρ := by
  unfold Kc
  have h1 : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR
  have h2 : (1 : ℝ) ≤ ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ dyExp (2 * R) ρ := Nat.cast_nonneg _
    nlinarith
  have h3 : (1 : ℝ) ≤ Real.exp (6 * lam N + 3) :=
    Real.one_le_exp (by have := lam_nonneg N; linarith)
  have h4 : (1 : ℝ) ≤ 16 * 3456 ^ 3 := by norm_num
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ 16 * 3456 ^ 3 * R ^ 3 * ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 * Real.exp (6 * lam N + 3) := by
        gcongr

/-- The toolkit with the J-ready form of Proposition 4.6. -/
def toolkit2Frozen : Prop :=
  ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ P, P = (fun (a b c : ℝ) (z : LeanEval.Analysis.WangZahlKakeya.Space) (e : LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) => {p : LeanEval.Analysis.WangZahlKakeya.Space | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}) → (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space), 0 < N → (∀ k, ‖w k‖ = 1) → (∀ k, T ρ (y k) (w k) ⊆ Metric.ball 0 R) → ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → LeanEval.Analysis.WangZahlKakeya.Space) (e : Fin L → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin N → Fin L), (N : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε * U.card ∧ 0 < m ∧ ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 * R ∧ (∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) ∧ (∀ k ∈ U, T ρ (y k) (w k) ⊆ P a b (2 * R) (z (g k)) (e (g k)) ∧ (Set.ncard {i | T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i)} : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε) ∧ (∀ i i', (Set.ncard {k | k ∈ U ∧ g k = i} : ℝ) ≤ C * ((N : ℝ) / ρ) ^ ε * Set.ncard {k | k ∈ U ∧ g k = i'}) ∧ (∀ i, m * (a * b * (2 * R)) ≤ C * ((N : ℝ) / ρ) ^ ε * (Set.ncard {k | k ∈ U ∧ g k = i} * ρ ^ 2)) ∧ (∀ V, Convex ℝ V → ENNReal.ofReal (Set.ncard {i | P a b (2 * R) (z i) (e i) ⊆ V} * (a * b * (2 * R))) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε) * MeasureTheory.volume V) ∧ ∀ i V, Convex ℝ V → ENNReal.ofReal (Set.ncard {k | k ∈ U ∧ g k = i ∧ T ρ (y k) (w k) ⊆ P a b (2 * R) (z i) (e i) ∩ V}) * MeasureTheory.volume (P a b (2 * R) (z i) (e i)) ≤ ENNReal.ofReal (C * ((N : ℝ) / ρ) ^ ε * Set.ncard {k | k ∈ U ∧ g k = i}) * MeasureTheory.volume (P a b (2 * R) (z i) (e i) ∩ V)) ∧ (∀ (U : Set LeanEval.Analysis.WangZahlKakeya.Space) (ν : LeanEval.Analysis.WangZahlKakeya.Space) (t₀ s τ : ℝ), Convex ℝ U → 0 < MeasureTheory.volume U → MeasureTheory.volume U ≠ ⊤ → 0 < s → 0 < τ → ENNReal.ofReal τ * MeasureTheory.volume U ≤ MeasureTheory.volume (U ∩ {p | |inner ℝ ν p - t₀| ≤ s}) → U ⊆ {p | |inner ℝ ν p - t₀| ≤ 48 * s / τ}) ∧ (∀ (W : Set LeanEval.Analysis.WangZahlKakeya.Space) (p : LeanEval.Analysis.WangZahlKakeya.Space) (r R : ℝ), Convex ℝ W → 0 < r → Metric.ball p r ⊆ W → W ⊆ Metric.ball 0 R → ∃ (a b c : ℝ) (e : LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space), 0 < a ∧ a ≤ b ∧ b ≤ c ∧ W ⊆ P a b c p e ∧ ENNReal.ofReal (a * b * c) ≤ 1728 * MeasureTheory.volume W) ∧ (∀ (n : ℕ) (F : Finset (Fin n)) (δ m l : ℝ) (z : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (e : Fin n → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < δ → δ ≤ 1 → 0 < m → 0 ≤ l → (∀ j ∈ F, MeasurableSet (Y j) ∧ Y j ⊆ P δ 1 1 (z j) (e j) ∧ ENNReal.ofReal (l * δ) ≤ MeasureTheory.volume (Y j)) → (∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {j | j ∈ F ∧ P δ 1 1 (z j) (e j) ⊆ W} * δ) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → l ^ 2 * δ * F.card ≤ 3456 * ((⌊Real.logb 2 (1 / δ)⌋₊ : ℝ) + 2) * m * (MeasureTheory.volume (⋃ j ∈ F, Y j)).toReal)

theorem toolkit2_frozen : toolkit2Frozen := by
  intro T hT P hP
  have hold := toolkit_frozen T hT P hP
  refine ⟨?_, hold.2.1, hold.2.2.1, hold.2.2.2⟩
  subst hT hP
  intro ε hε R hR
  obtain ⟨C', hC'1, hC'⟩ := Kc_le (ε / 3) (by positivity) R hR
  have hC'3 : (1 : ℝ) ≤ C' ^ 3 := one_le_pow₀ hC'1
  refine ⟨2 * C' ^ 3, by linarith, fun ρ hρ hρ1 N y w hN hw hball => ?_⟩
  have hF : Fam R ρ y w := ⟨hρ, hρ1, hw, hball⟩
  obtain ⟨U, m, a, b, L, z, e, g, h1, hm, ha, hab, hb, hKT, hcov, hbal, h45, hboxKT, hfrost⟩ :=
    hF.factor_assign hR hN
  set K := Kc R N ρ with hKdef
  have hK1 : 1 ≤ K := Kc_one_le hR N ρ
  set X : ℝ := (N : ℝ) / ρ with hX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hX1 : 1 ≤ X := by rw [hX, le_div_iff₀ hρ]; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                         linarith
  have hKC : K ≤ C' * X ^ (ε / 3) := hC' N hN ρ hρ hρ1
  have hXε : (X ^ (ε / 3)) ^ 3 = X ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; push_cast; ring
  have hK3 : 2 * K ^ 3 ≤ 2 * C' ^ 3 * X ^ ε := by
    have hK0 : 0 ≤ K := by linarith
    have : K ^ 3 ≤ (C' * X ^ (ε / 3)) ^ 3 := pow_le_pow_left₀ hK0 hKC 3
    rw [mul_pow, hXε] at this
    linarith
  have hKK : K ≤ 2 * K ^ 3 := by nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 1 ≤ 3)]
  have h2K : 2 * K ≤ 2 * K ^ 3 := by nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 1 ≤ 3)]
  have h2K2 : 2 * K ^ 2 ≤ 2 * K ^ 3 := by nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 2 ≤ 3)]
  set Kε := 2 * C' ^ 3 * X ^ ε with hKε
  have hKε1 : K ≤ Kε := hKK.trans hK3
  have hKε2 : 2 * K ≤ Kε := h2K.trans hK3
  have hKε3 : 2 * K ^ 2 ≤ Kε := h2K2.trans hK3
  have hKε4 : 2 * K ^ 3 ≤ Kε := hK3
  refine ⟨U, m, a, b, L, z, e, g, ?_, hm, ha, hab, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (N : ℝ) ≤ 2 * K * U.card := h1
      _ ≤ Kε * U.card := by gcongr
  · intro W hW
    beta_reduce
    rw [ncard_sub U W]
    exact hKT W hW
  · intro k hk
    beta_reduce
    refine ⟨(hcov k hk).1, ?_⟩
    rw [ncard_univ_filter]
    exact (hcov k hk).2.trans hKε1
  · intro i i'
    rw [ncard_filter_eq, ncard_filter_eq]
    exact (hbal i i').trans (mul_le_mul_of_nonneg_right hKε3 (Nat.cast_nonneg _))
  · intro i
    rw [ncard_filter_eq]
    refine (h45 i).trans ?_
    gcongr
  · intro V hV
    beta_reduce
    rw [ncard_univ_filter]
    refine (hboxKT V hV).trans ?_
    gcongr
  · intro i V hV
    change ENNReal.ofReal ((Set.ncard {k | k ∈ U ∧
        (g k = i ∧ tube ρ y w k ⊆ box a b (2 * R) (z i) (e i) ∩ V)} : ℝ)) *
        volume (box a b (2 * R) (z i) (e i)) ≤
      ENNReal.ofReal (Kε * (Set.ncard {k | k ∈ U ∧ g k = i} : ℝ)) *
        volume (box a b (2 * R) (z i) (e i) ∩ V)
    rw [ncard_filter_eq, ncard_filter_eq]
    refine (hfrost i V hV).trans ?_
    gcongr

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
