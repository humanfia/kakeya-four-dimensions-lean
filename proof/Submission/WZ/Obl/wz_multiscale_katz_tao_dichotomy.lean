-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_katz_tao_dichotomy.Tower
import Submission.WZ.Obl.wz_multiscale_finite_tower
import Submission.WZ.Obl.wz_tower_convex_count_composition
import Submission.WZ.Obl.wz_tower_balanced_refinement

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_multiscale_katz_tao_dichotomy`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_multiscale_katz_tao_dichotomy/`
belong to this obligation.
-/

theorem WangZahlLot.wz_multiscale_katz_tao_dichotomy : ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ K, K = (fun (d m : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ F, F = (fun (d l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ ENNReal.ofReal (l * n) * MeasureTheory.volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ∀ A, A = (fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * MeasureTheory.volume (T d (x i) (v i))) ∧ ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, MeasureTheory.volume (Y i) ∧ K d m n x v ∧ F d l n x v) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) → (∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ ζ) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧ T δ (x i) (v i) ⊆ T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r}}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤ ENNReal.ofReal (δ ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r})) → (∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (m : ℕ) (x' v' : Fin m → LeanEval.Analysis.WangZahlKakeya.Space) (Y' : Fin m → Set LeanEval.Analysis.WangZahlKakeya.Space) (M L : ℝ), A δ ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧ ENNReal.ofReal (δ ^ ε) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ j, MeasureTheory.volume (Y' j) ∧ ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < δ ^ (-ε) * ρ₀ ∧ ∃ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin m → Fin N), (∀ k, ‖w k‖ = 1) ∧ (∀ j, T δ (x' j) (v' j) ⊆ T ρ (y (f j)) (w (f j))) ∧ (∀ k k', (Set.ncard {j | f j = k} : ℝ) ≤ δ ^ (-ε) * Set.ncard {j | f j = k'}) ∧ K ρ (δ ^ (-ε)) N y w) := by
  intro σ ω hσ hσ' hω hω' T hT K hK F hF A hA hE hP ε hε
  subst T
  subst K
  subst F
  subst A
  obtain ⟨q, hq⟩ := exists_depth hω hω' (show 0 < ε / 4 by positivity)
  have hmesh : 2 * (1 - ω / 100) ^ q ≤ ε / 2 := by linarith
  have hmesh0 : 0 < 2 * (1 - ω / 100) ^ q := by
    apply mul_pos (by norm_num)
    exact pow_pos (by linarith) _
  obtain ⟨b, hb, hbε, d₁, hd₁, hbalance⟩ :=
    WangZahlLot.wz_tower_balanced_refinement (2 ^ q) ε
      volume rfl ENNReal.ofReal rfl Tube rfl ConvexCount rfl SlabCount rfl
      Admissibility rfl Tower rfl hε
  obtain ⟨t, ht, htb, d₀, hd₀, hcompose⟩ :=
    WangZahlLot.wz_tower_convex_count_composition (2 ^ q) b
      volume rfl ENNReal.ofReal rfl Tube rfl ConvexCount rfl Tower rfl hb
  obtain ⟨α, hα, κ, hκ, η, hη, hfinite⟩ :=
    WangZahlLot.wz_multiscale_finite_tower σ ω
      volume rfl ENNReal.ofReal rfl Tube rfl ConvexCount rfl SlabCount rfl
      Admissibility rfl Tower rfl (Large σ ω) rfl
      hσ hσ' hω hω' hE hP q t (min d₀ d₁) ht (lt_min hd₀ hd₁)
  refine ⟨α, hα, κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hfamily
  rcases hfinite δ hδ hδ100 n x v Y hfamily with hlarge | ⟨hsmall, hrefine⟩
  · exact Or.inl hlarge
  · obtain ⟨m, x', v', Y', M, L, hA', hUnion, hMass, hTower⟩ := hrefine
    have hglobal := hcompose δ hδ hδ100 (hsmall.trans (min_le_left _ _))
      (2 * (1 - ω / 100) ^ q) m x' v' hTower
    have hA'b : Admissibility δ b M L m x' v' Y' :=
      hA'.mono hδ (by linarith) htb le_rfl le_rfl
    obtain ⟨m', x'', v'', Y'', M', L', hA'', hUnion', hMass', hEvery⟩ :=
      hbalance δ hδ hδ100 (hsmall.trans (min_le_right _ _))
        (2 * (1 - ω / 100) ^ q) hmesh0 hmesh m x' v' Y' M L hA'b hglobal
    refine Or.inr ⟨m', x'', v'', Y'', M', L', hA'',
      hUnion'.trans hUnion, ?_, hEvery⟩
    exact retained_mass_trans hδ (by linarith) (by linarith) hMass hMass'
