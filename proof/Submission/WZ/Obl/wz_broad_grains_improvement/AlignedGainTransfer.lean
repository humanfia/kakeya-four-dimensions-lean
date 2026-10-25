-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedGainTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedAdmissible
import Submission.WZ.Obl.wz_multiscale_finite_tower.FiniteTower

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint VolumeBound)

/-- The geometric alignment used in the internal iteration does not involve
the shading or any of the error budgets. -/
def AlignedAxes {n : ℕ} (x v : Fin n → V) : Prop :=
  ∃ u : V, ∃ t : ℝ,
    (∀ i, ‖v i-u‖ ≤ 1/10) ∧
    (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1) ∧
    (∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t)

/-- A uniform gain restricted to aligned fine axes. -/
def AlignedGain (σ ω : ℝ) : Prop :=
  ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      VolumeBound σ ω κ α d n Y

/-- An aligned-family gain implies a gain for every admissible input. The
replacement's mass loss controls its cardinality loss, and costs at most half
of the exponent gain. -/
theorem volume_improvement_of_aligned {σ ω ε : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hgain : AlignedGain σ ω) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
        A d η (d^(-η)) (d^(-η)) n x v Y → VolumeBound σ ω κ α d n Y := by
  obtain ⟨α, κ, η₁, d₁, hα, hκ, hη₁, hd₁, hd₁small, Hgain⟩ := hgain
  let θ : ℝ := min η₁ (min ε (α/4))
  have hθ : 0 < θ := lt_min hη₁ (lt_min hε (by positivity))
  have hθη : θ ≤ η₁ := min_le_left _ _
  have hθε : θ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hθα : θ ≤ α/4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η, d₀, hη, hηθ, hd₀, hd₀d₁, hd₀small, Hprep⟩ :=
    prepare_aligned_admissible hθ hd₁
  let κ' : ℝ := κ*(1/56:ℝ)^(1-σ)
  have hκ' : 0 < κ' := by dsimp [κ']; positivity
  refine ⟨α/2, κ', η, d₀, by positivity, hκ', hη, hηθ.trans hθε,
    hd₀, hd₀d₁.trans hd₁small, ?_⟩
  intro d hd hdd n x v Y hA
  have hd1 : d ≤ 1 := (hdd.trans hd₀small).trans (by norm_num)
  obtain ⟨m, x', v', Z, u, t, hA', hF, _, hsub, hmass⟩ := Hprep d hd hdd n x v Y hA
  have haxes : AlignedAxes x' v' := ⟨u, t, hF.direction_cap,
    fun i => (hF.midpoint i).trans (by norm_num), hF.aligned⟩
  have hV := Hgain d hd (hdd.trans hd₀d₁) m x' v' Z
    (admissible_mono hd hd1 hθη hA') haxes
  have hbase : WangZahlLot.Obl.wz_multiscale_finite_tower.Admissible
      d η (d^(-η)) (d^(-η)) n x v Y := hA
  have hcard := hbase.aligned_retained_cardinality hF hd hd1 hmass
  have hV' := VolumeBound.of_refinement hd (by norm_num : (0:ℝ) < 1/56)
    hκ.le hA.1 hσ1 hcard hsub hV
  apply hV'.mono hd hd1 hκ'.le le_rfl
  have hcost : (η+θ)*(1-σ) ≤ η+θ := by
    nlinarith [mul_nonneg (show 0 ≤ η+θ by positivity) hσ]
  linarith

/-- The aligned internal gain route suffices for the frozen improvement,
regardless of the original grains state. -/
theorem improvement_of_aligned_gain {σ ω ζ ε : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hgain : AlignedGain σ ω) :
    L σ ω ζ ε := by
  obtain ⟨α, κ, η, d₀, hα, hκ, hη, hηε, hd₀, hd₀small, Hgain⟩ :=
    volume_improvement_of_aligned hσ hσ1 hε hgain
  exact ⟨α, κ, η, d₀, hα, hκ, hη, hηε, hd₀, hd₀small,
    fun d hd hdd n x v Y hA _ _ _ => Or.inl (Hgain d hd hdd n x v Y hA)⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
