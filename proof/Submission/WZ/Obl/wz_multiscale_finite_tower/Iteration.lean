-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Iteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Base
import Submission.WZ.Obl.wz_multiscale_finite_tower.Refinement

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The requested alternative at a specified finite depth. -/
def DepthProperty (σ ω : ℝ) (q : ℕ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
    Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
    VolumeBound σ ω κ α d n Y ∨
      (d ≤ D ∧ RetainedTower d ε (2 * (1 - ω / 100) ^ q) (2 ^ q) n Y)

/-- The endpoint estimate extends a sufficiently small scale dichotomy to all allowed scales,
while imposing any positive cutoff on the geometric alternative. -/
theorem Endpoint.attach_cutoff {σ ω ε g D : ℝ} {B : ℕ}
    (hE : Endpoint σ ω) (hσ : σ ≤ 1 / 2) (hD : 0 < D)
    (hsmall : ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
      ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → d ≤ d₀ → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y ∨ RetainedTower d ε g B n Y) :
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y ∨ (d ≤ D ∧ RetainedTower d ε g B n Y) := by
  obtain ⟨α, hα, κ₀, hκ₀, η₀, hη₀, d₀, hd₀, hsmall⟩ := hsmall
  obtain ⟨κ₁, hκ₁, η₁, hη₁, hlarge⟩ :=
    hE.away_from_zero hσ hα (lt_min hD hd₀)
  refine ⟨α, hα, min κ₀ κ₁, lt_min hκ₀ hκ₁, min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d ≤ 1 := by linarith
  by_cases hcut : d ≤ min D d₀
  · have hA₀ := hA.mono_error hd hd1 (min_le_left η₀ η₁)
    rcases hsmall d hd hd100 (hcut.trans (min_le_right D d₀)) n x v Y hA₀ with hV | hT
    · exact Or.inl (hV.mono hd hd1 (le_min hκ₀.le hκ₁.le) (min_le_left _ _) le_rfl)
    · exact Or.inr ⟨hcut.trans (min_le_left D d₀), hT⟩
  · have hA₁ := hA.mono_error hd hd1 (min_le_right η₀ η₁)
    have hV := hlarge d hd hd100 (le_of_not_ge hcut) n x v Y hA₁
    exact Or.inl (hV.mono hd hd1 (le_min hκ₀.le hκ₁.le) (min_le_right _ _) le_rfl)

/-- The depth-zero theorem supplies the initial case for any strengthened induction argument. -/
theorem depth_zero {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : σ ≤ 1 / 2) :
    DepthProperty σ ω 0 := by
  intro ε D hε hD
  exact finite_tower_base hE hσ hε hD

/-- Isolate the finite induction from its geometric scale-insertion step. -/
theorem all_depths_of_step {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : σ ≤ 1 / 2)
    (step : ∀ q : ℕ, DepthProperty σ ω q → DepthProperty σ ω (q + 1)) :
    ∀ q : ℕ, DepthProperty σ ω q := by
  intro q
  induction q with
  | zero => exact depth_zero hE hσ
  | succ q ih => exact step q ih

end WangZahlLot.Obl.wz_multiscale_finite_tower
