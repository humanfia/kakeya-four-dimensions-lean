import Submission.Obl.k4_finite_width_output_exclusion.Subsequence
import Submission.Obl.k4_scalar_linear_critical_extremizers.Horizon

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter Set

noncomputable section

lemma cost_nonneg {p : Data} (hp : Valid p) {h : ℝ} (hc : Cost p h) : 0 ≤ h := by
  obtain ⟨M, D, hc⟩ := (cost_iff p h).1 hc
  obtain ⟨k, κ, hκ, hKκ, hκε, a, hT, ha⟩ := (hc 1 zero_lt_one).exists
  have hN : 1 < p.N k := by linarith [hp.scale_ge_two k]
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ a.T := one_le_pow₀ (by norm_num)
  have hpow' : p.N k ^ (0 : ℝ) ≤ p.N k ^ h := by simpa using hpow.trans hT
  exact (Real.rpow_le_rpow_left_iff hN).1 hpow'

lemma costs_bddBelow {p : Data} (hp : Valid p) : BddBelow {h : ℝ | Cost p h} :=
  ⟨0, fun _ hh => cost_nonneg hp hh⟩

lemma costs_nonempty (hi : Initial) {p : Data} (hp : Valid p) :
    {h : ℝ | Cost p h}.Nonempty :=
  ⟨p.L + 1, hi p hp _ (by linarith)⟩

lemma horizon_le_cost {p : Data} (hp : Valid p) {h : ℝ} (hc : Cost p h) :
    Horizon p ≤ h := csInf_le (costs_bddBelow hp) hc

lemma horizon_reindex_le (hi : Initial) {p : Data} (hp : Valid p)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) : Horizon p ≤ Horizon (p.reindex φ) := by
  apply le_csInf (costs_nonempty hi (valid_reindex hp hφ))
  intro h hh
  exact horizon_le_cost hp (cost_of_reindex hφ hh)

lemma horizon_transfer (hi : Initial) {p q : Data} (hp : Valid p) (hq : Valid q)
    {a b : ℝ} (hb : 0 < b) (hlift : ∀ h : ℝ, Cost q h → Cost p (a + b * h)) :
    Horizon p ≤ a + b * Horizon q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨h, hh, hhε⟩ := exists_lt_of_csInf_lt (costs_nonempty hi hq)
    (lt_add_of_pos_right (Horizon q) (div_pos hε hb))
  have hbound := horizon_le_cost hp (hlift h hh)
  have hmul : b * h < b * (Horizon q + ε / b) := mul_lt_mul_of_pos_left hhε hb
  have hid : b * (Horizon q + ε / b) = b * Horizon q + ε := by field_simp
  rw [hid] at hmul
  linarith

lemma horizon_composition_le (hi : Initial) {p q : Data} (hp : Valid p) (hq : Valid q)
    {h : ℝ} (hlift : ∀ h' e : ℝ, 0 < e → Cost q h' → Cost p (h + h' + e)) :
    Horizon p ≤ h + Horizon q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hx := horizon_transfer hi hp hq (a := h + ε) (b := 1) zero_lt_one
    (fun h' hh => by simpa only [one_mul, add_right_comm] using hlift h' ε hε hh)
  linarith

lemma narrow_mono {p : Data} (hp : Valid p) {h h' w w' : ℝ}
    (hh : h ≤ h') (hw : w' ≤ w) (hn : Narrow p h w) : Narrow p h' w' := by
  rw [narrow_iff] at hn ⊢
  obtain ⟨M, D, hn⟩ := hn
  refine ⟨M, D, fun ε hε => (hn ε hε).mono ?_⟩
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, haw, ha⟩
  refine ⟨κ, hκ, hKκ, hκε, a, hT.trans ?_, fun b => (haw b).trans ?_, ha⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)

end
end Submission.Obl.k4_finite_width_output_exclusion
