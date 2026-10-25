import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Sample
import Submission.Obl.k4_quadratic_finite_greedy_cover.PathFacts

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

/-- Uniform discovery under the original laws supplies the finite mixed cover. -/
theorem prove_statement : Statement := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ₁ hκ₁' hℓ hS hS' hη hρ hρ'
  intro m s gain δ₀ hgrid hgain hgain' hδ₀ hδ₀' hdisc
  intro N K L d W ω ν E P B f g G hprob hlinear Mp Dp
  obtain ⟨hN₂,hNt,hL,hω,hωsum,hν,hB,hE⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G hprob
  have hN (k : ℕ) : 1 ≤ N k := by linarith [hN₂ k]
  obtain ⟨Mc,hdiscovery⟩ := hdisc N K L d W ω ν E P B f g G hprob hlinear Mp Dp
  obtain ⟨M,hM,hmenu⟩ := geometric_menu gain ρ hgain hρ
  let a := (d₁ + ρ) / 8 * L
  let Mg := max Mc ⌈2 * (Mp : ℝ) + a + 3⌉₊
  let Dg := max Dp 4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hMg : 2 * (Mp : ℝ) + a + 3 ≤ (Mg : ℝ) :=
    (Nat.le_ceil _).trans (by dsimp [Mg]; exact_mod_cast Nat.le_max_right Mc ⌈2 * (Mp : ℝ) + a + 3⌉₊)
  refine ⟨Mg,Dg,?_⟩
  intro ε hε hε'
  let εin := ε / 8
  have hein : 0 < εin := by dsimp [εin]; positivity
  have hein' : εin ≤ ε := by dsimp [εin]; linarith
  obtain ⟨σd,hσd,kd,hdiscd⟩ := hdiscovery εin hein
  let D := ((m * M * 2 : ℕ) : ℝ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.mul_pos (Nat.mul_pos hgrid.1.1 hM) (by omega : 0 < 2)
  obtain ⟨σb,hσb,hbudget⟩ := Submission.Obl.k4_quadratic_finite_greedy_cover.eventual_coverage_budget
    N hN hNt (ρ * gain * L / 3) ε D (by positivity) hε hD
  let σ := min σd σb
  obtain ⟨kb,hkb⟩ := Filter.eventually_atTop.mp (hbudget.and (hNt.eventually_ge_atTop (194 : ℝ)))
  refine ⟨σ,lt_min hσd hσb,max kd kb,?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp
  have (w : Fin (W k)) : IsProbabilityMeasure (ν k w) := hν k w
  have hkd : kd ≤ k := (Nat.le_max_left _ _).trans hk
  have hkbk : kb ≤ k := (Nat.le_max_right _ _).trans hk
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hp.1
  have hκbudget : κ ≤ N k ^ σb := hp.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_right _ _))
  have hb : 2 ≤ N k ^ (ρ * gain * L / 3) ∧ 2 ≤ N k ^ ε ∧
      N k ^ (-ε) ≤ (κ⁻¹ / 2) / D - 8 / (N k ^ (ρ * gain * L / 3)) ^ 3 := by
    simpa only [add_zero] using (hkb k hkbk).1 κ 0 hκpos hκbudget (by norm_num)
  have hpd : pathP ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σd
      r T nw κ C lev par γ j c u Q R A F lst :=
    ⟨hp.1,hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_left _ _)),hp.2.2⟩
  have hdiscH := hdiscd k hkd r T nw κ C lev par γ j c u Q R A F lst hpd
  rcases hp with ⟨hκ,hκN,hC,hend,hlevels,hlists,hold,hnodes⟩
  have hAm (b : Fin C) : MeasurableSet (A b) := by
    rcases (hnodes b).2.2 with ⟨_,_,_,_,_,_,hA,_⟩
    exact hA
  have hFm (b : Fin C) : MeasurableSet (F b) := by
    rcases (hnodes b).2.2 with ⟨_,_,_,_,_,_,_,hF,_⟩
    exact hF
  have hFsub (b : Fin C) : F b ⊆ E k (γ b) := by
    rcases (hnodes b).2.2 with ⟨_,_,_,_,_,_,_,_,_,_,hF,_⟩
    exact fun p hp => (hF p hp).1
  have hFblock (b : Fin C) : ∀ p ∈ F b, p.1 ∈ A b ∧ p.2 ∈ block T lev j b := by
    rcases (hnodes b).2.2 with ⟨_,_,_,_,_,_,_,_,_,_,hF,_⟩
    exact fun p hp => ⟨(hF p hp).2.1,(hF p hp).2.2.1⟩
  have hAfmt (b : Fin C) (q : ℕ) : fmt 6 (N k ^ Mp) Dp {w | (q,w) ∈ A b} := by
    rcases (hnodes b).2.2 with ⟨_,_,_,_,_,_,_,_,hfmt,_⟩
    exact (hfmt q).1
  have hApos (b : Fin C) : 0 < (ν k (γ b)).real (A b) := by
    rcases (hnodes b).2.2 with ⟨hdet,_,_,_,_,_,_,_,_,_,hF,hex⟩
    have hmupos : 0 < (ν k (γ b)).prod volume (F b) := by
      apply lt_of_lt_of_le _ hex.1
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith [hN₂ k]) _) (abs_pos.mpr hdet))
        (mul_pos (by positivity) hκpos)
    have hA0 : ν k (γ b) (A b) ≠ 0 := by
      intro hz
      have hbnd : (ν k (γ b)).prod volume (F b) ≤ ν k (γ b) (A b) *
          volume (block T lev j b) := by
        apply (measure_mono (show F b ⊆ A b ×ˢ block T lev j b from hFblock b)).trans
        exact Measure.prod_prod_le _ _
      rw [hz,zero_mul] at hbnd
      exact (not_le_of_gt hmupos) hbnd
    exact ENNReal.toReal_pos hA0 (by finiteness)
  let H := termInc (W k) C m lev γ F
  have hHm (w : Fin (W k)) : MeasurableSet (H w) :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.terminalUnion_measurable (W k) C m lev γ F hFm w
  have hHsub (w : Fin (W k)) : H w ⊆ E k w :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.terminalUnion_subset (W k) C m lev γ F (E k) hFsub w
  have hHfin (w : Fin (W k)) : (ν k w).prod volume (H w) ≠ ∞ :=
    measure_ne_top_of_subset ((hHsub w).trans (hE k w)) (by simp)
  have hHmassENN : ENNReal.ofReal κ⁻¹ ≤ ∑ w,ENNReal.ofReal (ω k w) * (ν k w).prod volume (H w) := by
    have heq := Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask_mass (ν k)
      (fun w => ENNReal.ofReal (ω k w)) (m-1) (T (m-1)) lev γ j A F
      (fun b _ => hFm b) (fun b hb p hp => by simpa only [block,hb] using hFblock b p hp)
      (fun b b' hb hb' hne hw hj' => hold b b' hne (hb.trans hb'.symm) hw hj')
    calc
      _ ≤ ∑ b,if lev b = m-1 then ENNReal.ofReal (ω k (γ b)) * (ν k (γ b)).prod volume (F b) else 0 :=
        (hlevels (m-1) (by have := hgrid.1.1; omega)).2.2.2.2.2
      _ = ∑ w,ENNReal.ofReal (ω k w) * (ν k w).prod volume
          (Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask (m-1) (T (m-1)) lev γ j F w) := heq.symm
      _ ≤ _ := Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (measure_mono
        (Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask_subset _ _ _ _ _ _ w)))
  have hHmass : κ⁻¹ ≤ ∑ w,ω k w * ((ν k w).prod volume).real (H w) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun w _ => mul_nonneg (hω k w) measureReal_nonneg))).mp
    rw [Submission.Obl.k4_quadratic_finite_greedy_cover.ofReal_weighted_mass
      (fun w => (ν k w).prod volume) (ω k) H (hω k) hHfin]
    exact hHmassENN
  have hdiscReal : ∀ H' : Fin (W k) → Set Incidence,
      (∀ w,MeasurableSet (H' w) ∧ H' w ⊆ H w) →
      (∑ w,ω k w * ((ν k w).prod volume).real (H w)) / 2 ≤
        ∑ w,ω k w * ((ν k w).prod volume).real (H' w) →
      cand (N k) L (W k) (ν k) (B k) Mc d₁ ρ gain εin r T C lev γ j u Q A H' := by
    intro H' hH' hmass
    apply hdiscH H' hH'
    rw [← Submission.Obl.k4_quadratic_finite_greedy_cover.ofReal_weighted_mass
      (fun w => (ν k w).prod volume) (ω k) H (hω k) hHfin,
      ← Submission.Obl.k4_quadratic_finite_greedy_cover.ofReal_weighted_mass
        (fun w => (ν k w).prod volume) (ω k) H' (hω k)
        (fun w => measure_ne_top_of_subset (hH' w).2 (hHfin w))]
    have hhalf (t : ℝ) : (1/2 : ENNReal) * ENNReal.ofReal t = ENNReal.ofReal (t / 2) := by
      rw [ENNReal.ofReal_div_of_pos (zero_lt_two : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
      simp only [div_eq_mul_inv,one_mul]
      exact mul_comm _ _
    rw [hhalf]
    exact ENNReal.ofReal_le_ofReal hmass
  exact sample_cover (N k) L d₁ ρ gain εin ε κ (ν k) (ω k) (B k) r T lev j γ u Q A F
    (hkb k hkbk).2 hL hd hd'.le hρ hρ' hgain hein.le hein' hε' hκpos (hν k) (hω k)
    (hωsum k) (hB k) hgrid.1.1 hM hmenu hAm hApos hAfmt (fun b => (hnodes b).1)
    (fun b => (hnodes b).2.1) hold hHm hHfin hHmass hdiscReal hC (Nat.le_max_left _ _)
    le_rfl hMg hb.1 hb.2.1 hb.2.2

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
