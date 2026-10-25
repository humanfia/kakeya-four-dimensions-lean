-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.FromFixedExponents.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.UniformExponents
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.LowRangeFinal

/-!
# o157 from estimates at fixed exponents in the high range

The analytic input may choose its gain, error allowance and scale separately
for each fixed exponent `s` in `[1/2, 1)`. No quantitative dependence on `s`
or uniformity near `1/2` is assumed. The low range, exponent stability and
compactness then give the literal frozen statement.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- The fixed-exponent form of the remaining analytic input. -/
def FixedHighRangeSeparatedCore : Prop :=
  ∀ s : ℝ, 1 / 2 ≤ s → s < 1 → ∃ ε₀ η r₀ : ℝ,
    0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → SeparatedFurstenbergAt r s ε₀ η

lemma fixed_separated_of_high (h : FixedHighRangeSeparatedCore)
    {s : ℝ} (hs : 1 / 4 ≤ s) (hsone : s < 1) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → SeparatedFurstenbergAt r s ε₀ η := by
  by_cases hhalf : 1 / 2 ≤ s
  · exact h s hhalf hsone
  · obtain ⟨ε₀, η, r₀, hε₀, hη, hr₀, hlow⟩ :=
      furstenberg_low_range (1 / 2 - s) (by linarith)
    refine ⟨ε₀, η, r₀, hε₀, hη, hr₀, ?_⟩
    intro r hr hrr P D hPfin hPne hDfin hPnorm hPsep hPfr hDmem hbush hsep hKT
    exact hlow r s hr hrr hs (by linarith) P D hPfin hPne hDfin hPnorm
      hPfr hDmem hbush hsep hKT

lemma uniform_separated_of_fixed_high (h : FixedHighRangeSeparatedCore) :
    ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε →
        SeparatedFurstenbergAt r σ ε₀ η := by
  intro ε hε
  obtain ⟨ε₀, η, r₀, hε₀, hη, hr₀, hU⟩ :=
    uniform_separated_furstenberg_on_Icc (a := 1 / 4) (b := 1 - ε) (by norm_num)
      (fun s hs => fixed_separated_of_high h hs.1 (by linarith [hs.2]))
  exact ⟨ε₀, η, r₀, hε₀, hη, hr₀,
    fun r σ hr hrr hσlo hσhi => hU r σ hr hrr ⟨hσlo, hσhi⟩⟩

/-- The full frozen bush estimate follows from its separated-point version
at each fixed exponent in `[1/2, 1)`. -/
theorem furstenberg_of_fixed_high (h : FixedHighRangeSeparatedCore) : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) :=
  furstenberg_of_separated (uniform_separated_of_fixed_high h)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
