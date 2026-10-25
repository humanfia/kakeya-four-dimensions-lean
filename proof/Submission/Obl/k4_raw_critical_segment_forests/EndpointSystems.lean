import Submission.Obl.k4_raw_critical_segment_forests.RawOneLayer
import Submission.Obl.k4_raw_critical_segment_forests.AtlasDepth

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A narrow family above the horizon has bounded exact width exponents and
both time bounds, at a fixed format. -/
theorem endpoint_systems {p : Data} (hp : Valid p) {hlo h hhi v q : ℝ}
    (hloH : hlo < Horizon p) (hhh : h < hhi) (hq : 0 < q)
    (hn : Narrow p h v) :
    ∃ M D : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
      ∃ (κ : ℝ) (a : Atlas p k) (width : Fin a.C → ℝ),
        1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ σ ∧ a.TrueAt M D κ ∧
        p.N k ^ hlo ≤ (2 : ℝ) ^ a.T ∧ (2 : ℝ) ^ a.T ≤ p.N k ^ hhi ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ M ∧
        ∀ b, |width b| ≤ (M : ℝ) ∧
          p.N k ^ (-width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ∧
          v - q ≤ width b := by
  obtain ⟨M₀, D, hsys⟩ := (narrow_iff p h v).mp hn
  obtain ⟨τ₀, hτ₀, hguard⟩ := eventually_no_short_true_atlas hp hloH M₀ D
  obtain ⟨M₁, hM₁⟩ := exists_nat_ge hhi
  let M := 2 * M₀ + 2 + M₁
  have hM : M₀ ≤ M := by dsimp [M]; omega
  have hMw : 2 * M₀ + 2 ≤ M := by dsimp [M]; omega
  have hhM : hhi ≤ (M : ℝ) := hM₁.trans (by exact_mod_cast
    (show M₁ ≤ M by dsimp [M]; omega))
  refine ⟨M, D, ?_⟩
  intro σ hσ
  let τ := min σ (min τ₀ (min q (min 1 (hhi - h))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτσ : τ ≤ σ := min_le_left _ _
  have hτg : τ ≤ τ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hτq : τ ≤ q :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ1 : τ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hτh : τ ≤ hhi - h :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  apply ((hsys τ hτ).and_eventually hguard).mono
  rintro k ⟨⟨κ, hκ, hK, hκN, a, hT, hdet, ha⟩, hg⟩
  have hN : 1 < p.N k := by linarith [hp.scale_ge_two k]
  have hex := fun b => chart_log_width hN (by linarith : 0 ≤ κ) hκN hτ1
    (ha.2.2.1 b)
  choose width hw using hex
  have hThi : (2 : ℝ) ^ a.T ≤ p.N k ^ hhi := hT.trans
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
  refine ⟨κ, a, width, hκ, hK, hκN.trans
    (Real.rpow_le_rpow_of_exponent_le hN.le hτσ),
    trueAt_mono_format hp (by linarith) hM ha, ?_, hThi, ?_, ?_⟩
  · exact (hg κ a hκ hK (hκN.trans
      (Real.rpow_le_rpow_of_exponent_le hN.le hτg)) ha).le
  · exact hThi.trans (by rw [← Real.rpow_natCast]; exact
      Real.rpow_le_rpow_of_exponent_le hN.le hhM)
  · intro b
    exact ⟨(hw b).1.trans (by exact_mod_cast hMw), (hw b).2,
      (by linarith : v - q ≤ v - τ).trans
        (width_exponent_lower hN (hw b).2 (hdet b))⟩

lemma oneLayerForest_core_depth {p : Data} {k M D : ℕ} {κ r : ℝ}
    {a : Atlas p k} (hκ : 1 ≤ κ) (hK : p.K k ≤ κ)
    (ha : TrueDepth a M D κ r) :
    (oneLayerForest a κ).Core M D 1 (fun _ => r) := by
  obtain ⟨hC, hsep, hchart, hmass⟩ := ha
  refine ⟨hκ, hK, hC, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change ENNReal.ofReal κ⁻¹ ≤ ∑ b : Fin a.C, if (0 : ℕ) = 0 then
      ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) else 0
    simpa only [ite_true] using hmass
  · intro b b' hbb' _ hγ hj
    exact hsep b b' hbb' hγ (Fin.ext hj)
  · intro b
    exact ⟨Nat.zero_lt_succ 0, (a.j b).isLt, hchart b,
      fun hb => False.elim (Nat.not_lt_zero _ hb)⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
