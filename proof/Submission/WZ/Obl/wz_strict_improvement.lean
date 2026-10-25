-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_all_scales_volume
import Submission.WZ.Obl.wz_sticky_katz_tao_every_scale
import Submission.WZ.Obl.wz_refined_induction_on_scales
import Submission.WZ.Obl.wz_multiscale_katz_tao_dichotomy
import Submission.WZ.Obl.wz_strict_improvement.Combination
import Submission.WZ.Obl.wz_strict_improvement.TubeVolume
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_strict_improvement`

Glue of the split of o005 (Wang–Zahl, Proposition 1.7, restricted to `0 < σ ≤ 1/2`,
`0 < ω ≤ 1`). It is the paper's "Proof of Proposition 1.7" (§11):

* `wz_sticky_katz_tao_every_scale` applied to `wz_frostman_all_scales_volume` (o015, reused from
  o004's split) is Theorem 10.2 (Theorem 6.2 + Nikishin–Stein–Pisier factorization);
* `wz_multiscale_katz_tao_dichotomy` applied to `wz_refined_induction_on_scales` is Lemma 11.2
  (Proposition 9.1 + the multiscale analysis);
* the numerical combination: Lemma 11.2 with `ε = min(η₁, ω/8)`, where `η₁` comes from
  Theorem 10.2 with `ε = ω/4`, gives the gain `g = min(α, ω/4)`.

The numerical helpers (`Estimates`, `Slab`, `TubeVolume`, `Comparison`, `Combination`) were
written by session x0009. See `.lot/notes` and the split's `PROOF.md`.
-/

namespace WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- Admissible, `δ^η`-dense, with Katz–Tao count `m` and Frostman slab count `l`: the bundled
hypotheses (`A` in the statements of the §§9–11 children, with `T`, `K`, `F` instantiated). -/
abbrev Adm (d η m l : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧
      Y i ⊆ Tube d (x i) (v i)) ∧
    (∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
      1 / 2 * volume (Tube d (x i) (v i))) ∧
    Dense d η Y ∧ KatzTao d m x v ∧ FrostmanSlab d l x v

/-- `E(σ,ω)` with bundled hypotheses, as in the statements of the §§9–11 children. -/
abbrev EAdm (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Adm δ η m l n x v Y → ENNReal.ofReal (ELower σ ω a ε δ m l n) ≤ volume (⋃ i, Y i)

theorem eAdm_of_e {σ ω : ℝ} (hE : E σ ω) : EAdm σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hA
  obtain ⟨hn, hi, hdist, hdense, hK, hF⟩ := hA
  exact h δ hδ hδmax m l hm hl n x v Y hn (fun i => (hi i).1) (fun i => (hi i).2.1) hdist
    (fun i => (hi i).2.2.1) (fun i => (hi i).2.2.2) hdense hK hF

/-- Katz–Tao convex Wolff axioms at every scale with error `K` (assignment form). -/
abbrev KTEvery {n : ℕ} (δ K : ℝ) (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < K * ρ₀ ∧
    ∃ (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N),
      (∀ k, ‖w k‖ = 1) ∧ (∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) ∧
      (∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ K * Set.ncard {i | f i = k'}) ∧
      KatzTao ρ K y w

theorem ktEvery_mono {n : ℕ} {δ K₁ K₂ : ℝ} {x v : Fin n → Space} (hδ : 0 < δ)
    (hK : K₁ ≤ K₂) (h : KTEvery δ K₁ x v) : KTEvery δ K₂ x v := by
  intro ρ₀ hρ₀ hρ₁
  obtain ⟨ρ, h1, h2, N, y, w, f, hw, hcov, hbal, hkt⟩ := h ρ₀ hρ₀ hρ₁
  have hρ₀pos : 0 ≤ ρ₀ := hδ.le.trans hρ₀
  refine ⟨ρ, h1, h2.trans_le (mul_le_mul_of_nonneg_right hK hρ₀pos), N, y, w, f, hw, hcov,
    fun k k' => (hbal k k').trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)),
    katzTao_mono hK hkt⟩

end WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory WangZahlLot.Obl.wz_strict_improvement in
theorem WangZahlLot.wz_strict_improvement : ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (m) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((l) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (- (3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) → ∃ g : ℝ, 0 < g ∧ g ≤ ω ∧ (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((δ ^ (-η)) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω - g) + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) := by
  intro σ ω hσ hσ₂ hω hω₁ hE
  have hE' : EAdm σ ω := eAdm_of_e hE
  -- Lemma 11.2 (multiscale dichotomy), from Proposition 9.1.
  have hL := WangZahlLot.wz_multiscale_katz_tao_dichotomy σ ω hσ hσ₂ hω hω₁ _ rfl _ rfl _ rfl _ rfl
    hE' (WangZahlLot.wz_refined_induction_on_scales σ ω hσ hσ₂ hω hω₁ _ rfl _ rfl _ rfl _ rfl hE')
  -- Theorem 10.2 (sticky Kakeya for Katz–Tao at every scale), from Theorem 6.2.
  have hT := WangZahlLot.wz_sticky_katz_tao_every_scale _ rfl WangZahlLot.wz_frostman_all_scales_volume
  obtain ⟨κ₁, hκ₁, η₁, hη₁, hS⟩ := hT (ω / 4) (by positivity)
  set θ := min η₁ (ω / 8) with hθdef
  have hθ : 0 < θ := lt_min hη₁ (by positivity)
  have hθη₁ : θ ≤ η₁ := min_le_left _ _
  have hθω : θ ≤ ω / 8 := min_le_right _ _
  obtain ⟨α, hα, κ₂, hκ₂, η₂, hη₂, hL'⟩ := hL θ hθ
  obtain ⟨g, η, hg, hgω, hgα, hgω4, hη, hηη₀, hησ⟩ :=
    improvement_parameters (σ := σ) (ω := ω) (α := α) (η₀ := min η₂ (ω / 8)) hσ.le hω hα
      (lt_min hη₂ (by positivity))
  have hηη₂ : η ≤ η₂ := hηη₀.trans (min_le_left _ _)
  have hηω : η ≤ ω / 8 := hηη₀.trans (min_le_right _ _)
  refine ⟨g, hg, hgω, ?_⟩
  intro ε hε
  refine ⟨min κ₂ (κ₁ / 8 * (8 : ℝ) ^ (-σ)), lt_min hκ₂ (by positivity), η, hη, ?_⟩
  intro δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub hdense hK hF
  have hδ₁ : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hcard : δ ^ η ≤ 8 * ((n : ℝ) * δ) := frostman_cardinality_lower hδ hn hv hball hF
  have hm : δ ^ (-η) ≤ δ ^ (-η₂) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hηη₂)
  have hAdm : Adm δ η₂ (δ ^ (-η₂)) (δ ^ (-η₂)) n x v Y :=
    ⟨hn, fun i => ⟨hv i, hball i, hmeas i, hsub i⟩, hdistinct,
      dense_mono hδ hδ₁ hηη₂ hdense, katzTao_mono hm hK, frostmanSlab_mono hm hF⟩
  apply combine_volume_alternative (α := α) (η := η) (b := κ₁ / 8) hσ.le hκ₂ (by positivity)
    hgα hgω4 hησ hε.le hδ hδ₁ hn hcard
  rcases hL' δ hδ hδmax n x v Y hAdm with hA | ⟨m, x', v', Y', M, L, hA', hU, hret, hkt⟩
  · left
    simpa only [DLower, add_zero] using hA
  · right
    obtain ⟨hm0, hi', hdist', hdense', -, -⟩ := hA'
    have hkt' : KTEvery δ (δ ^ (-η₁)) x' v' :=
      ktEvery_mono hδ (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hθη₁)) hkt
    have hS' := hS δ hδ hδmax m x' v' Y' hm0 (fun j => (hi' j).1) (fun j => (hi' j).2.1) hdist'
      (fun j => (hi' j).2.2.1) (fun j => (hi' j).2.2.2) (dense_mono hδ hδ₁ hθη₁ hdense') hkt'
    have hcount : δ ^ (η + θ) * (n : ℝ) ≤ 8 * (m : ℝ) :=
      cardinality_of_retained_mass hδ (by linarith) (fun j => (hi' j).1) (fun j => (hi' j).2.2.2)
        hdense hret
    have hpow : δ ^ (ω / 2) ≤ δ ^ (ω / 4) * δ ^ (η + θ) := by
      rw [← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (by linarith)
    calc ENNReal.ofReal (κ₁ / 8 * δ ^ (ω / 2) * ((n : ℝ) * δ ^ 2))
        ≤ ENNReal.ofReal (κ₁ * δ ^ (ω / 4) * ((m : ℝ) * δ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          calc κ₁ / 8 * δ ^ (ω / 2) * ((n : ℝ) * δ ^ 2)
              ≤ κ₁ / 8 * (δ ^ (ω / 4) * δ ^ (η + θ)) * ((n : ℝ) * δ ^ 2) := by gcongr
            _ = κ₁ / 8 * δ ^ (ω / 4) * (δ ^ (η + θ) * (n : ℝ)) * δ ^ 2 := by ring
            _ ≤ κ₁ / 8 * δ ^ (ω / 4) * (8 * (m : ℝ)) * δ ^ 2 := by gcongr
            _ = κ₁ * δ ^ (ω / 4) * ((m : ℝ) * δ ^ 2) := by ring
      _ ≤ volume (⋃ j, Y' j) := hS'
      _ ≤ volume (⋃ i, Y i) := measure_mono hU
