-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PhysicalDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PhysicalHierarchy
import Submission.WZ.Obl.wz_multiscale_katz_tao_dichotomy.Tower
import Submission.WZ.Obl.wz_tower_convex_count_composition
import Submission.WZ.Obl.wz_tower_balanced_refinement

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy

set_option maxHeartbeats 1200000

/-- A retained admissible family satisfying the Katz--Tao convex count at every scale. -/
def RetainedEveryScale (d ε : ℝ) {n : ℕ} (Y : Fin n → Set Space) : Prop :=
  ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
    Admissibility d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
    ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
    KatzTaoEveryScale d ε x' v'

/-- The all-scales alternative needed by the sticky estimate. -/
def EveryScaleAlternative (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
    Admissibility d η (d ^ (-η)) (d ^ (-η)) n x v Y →
    Large σ ω κ α d n Y ∨ RetainedEveryScale d ε Y

/- This generalizes the final composition in accepted o020,
WangZahlLot/Obl/wz_multiscale_katz_tao_dichotomy.lean. The premise is the
unrestricted physical alternative; all tower composition and balancing results
are imported from the accepted library. -/
theorem every_scale_alternative_of_physical {σ ω : ℝ}
    (hE : WangZahlLot.Obl.wz_multiscale_finite_tower.Endpoint σ ω)
    (hStep : PhysicalStep σ ω) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω' : ω ≤ 1) : EveryScaleAlternative σ ω := by
  intro ε hε
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
    finite_tower_all_depths_of_physical hE hStep hσ.le hσ' hω hω' q
      t (min d₀ d₁) ht (lt_min hd₀ hd₁)
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

end WangZahlLot.Obl.wz_broad_grains_improvement
