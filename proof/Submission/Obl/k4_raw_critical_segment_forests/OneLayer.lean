import Submission.Obl.k4_raw_critical_segment_forests.HorizonGuard
import Submission.Obl.k4_raw_critical_segment_forests.Widths

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

lemma trueAt_mono_format {p : Data} (hp : Valid p) {k M M' D : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (hM : M ≤ M') {a : Atlas p k} (ha : a.TrueAt M D κ) :
    a.TrueAt M' D κ := by
  obtain ⟨hC, hsep, hchart, hmass⟩ := ha
  have hpoly : p.N k ^ M ≤ p.N k ^ M' :=
    pow_le_pow_right₀ (hp.scale_ge_one k) hM
  refine ⟨hC.trans hpoly, hsep, ?_, hmass⟩
  intro b
  exact chart_transport hpoly hκ le_rfl (hp.B_pos k (a.γ b)).le
    le_rfl le_rfl id (hchart b)

/-- Uniform availability gives exact one-layer raw forests. In particular,
near-maximality supplies the lower as well as the upper dyadic time cost. -/
theorem one_layer_systems {ds kr S η w ε q : ℝ}
    (hkr : kr ≤ 1) (hunif : UniformWidth ds kr S η w)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p →
      p.L = 1 → p.S = S → p.η = η →
      p.d < ds + t → kr - t < Horizon p →
      ∃ M D : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
        ∃ (κ : ℝ) (a : Atlas p k) (width : Fin a.C → ℝ),
          1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ σ ∧ a.TrueAt M D κ ∧
          p.N k ^ (kr - ε) ≤ (2 : ℝ) ^ a.T ∧
          (2 : ℝ) ^ a.T ≤ p.N k ^ (kr + ε) ∧
          (2 : ℝ) ^ a.T ≤ p.N k ^ M ∧
          ∀ b, |width b| ≤ (M : ℝ) ∧
            p.N k ^ (-width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ∧
            w - q ≤ width b := by
  obtain ⟨t₀, ht₀, hwidth⟩ := hunif (ε / 4) (by positivity)
  let t := min t₀ (ε / 2)
  have ht : 0 < t := lt_min ht₀ (by positivity)
  refine ⟨t, ht, ?_⟩
  intro p hp hpL hpS hpη hpd hpH
  have hpt : p.d < ds + t₀ := lt_of_lt_of_le hpd (by dsimp [t]; linarith [min_le_left t₀ (ε / 2)])
  have hpHt : kr - t₀ < Horizon p := lt_of_le_of_lt (by
    dsimp [t]; linarith [min_le_left t₀ (ε / 2)]) hpH
  obtain ⟨M₀, D, hsys⟩ := (narrow_iff p (kr + ε / 4) w).1
    (hwidth p hp hpL hpS hpη hpt hpHt)
  have hshort : kr - ε < Horizon p := by
    have := min_le_right t₀ (ε / 2)
    dsimp [t] at hpH
    linarith
  obtain ⟨τ₀, hτ₀, hguard⟩ := eventually_no_short_true_atlas hp hshort M₀ D
  let M := 2 * M₀ + 2
  have hM : M₀ ≤ M := by dsimp [M]; omega
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
    dsimp [M]
    exact_mod_cast (show 2 ≤ 2 * M₀ + 2 by omega)
  refine ⟨M, D, ?_⟩
  intro σ hσ
  let τ := min σ (min τ₀ (min q (min 1 (ε / 4))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτσ : τ ≤ σ := min_le_left _ _
  have hτg : τ ≤ τ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hτq : τ ≤ q :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ1 : τ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hτε : τ ≤ ε / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  apply ((hsys τ hτ).and_eventually hguard).mono
  rintro k ⟨⟨κ, hκ, hKκ, hκτ, a, hT, hdet, ha⟩, hguardk⟩
  have hN : 1 < p.N k := by linarith [hp.scale_ge_two k]
  have hNpos : 0 < p.N k := by linarith
  have hchart := ha.2.2.1
  have hex : ∀ b : Fin a.C, ∃ v : ℝ, |v| ≤ (2 * M₀ + 2 : ℕ) ∧
      p.N k ^ (-v) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T :=
    fun b => chart_log_width hN (by linarith) hκτ hτ1 (hchart b)
  choose v hv using hex
  refine ⟨κ, a, v, hκ, hKκ,
    hκτ.trans (Real.rpow_le_rpow_of_exponent_le hN.le hτσ),
    trueAt_mono_format hp (by linarith) hM ha, ?_, ?_, ?_, ?_⟩
  · exact (hguardk κ a hκ hKκ
      (hκτ.trans (Real.rpow_le_rpow_of_exponent_le hN.le hτg)) ha).le
  · exact hT.trans (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
  · apply hT.trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    linarith
  · intro b
    exact ⟨(hv b).1, (hv b).2,
      (by linarith : w - q ≤ w - τ).trans
        (width_exponent_lower hN (hv b).2 (hdet b))⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
