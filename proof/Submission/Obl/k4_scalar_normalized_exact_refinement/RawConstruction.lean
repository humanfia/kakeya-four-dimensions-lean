import Submission.Obl.k4_scalar_normalized_exact_refinement.ChosenCharts

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set Filter
open k4_scalar_linear_critical_extremizers.Split
open scoped ENNReal

noncomputable section

namespace ChosenCharts

variable {p : Code} {r b h : ℝ} (a : ChosenCharts p r b h)

lemma θ_measurable (k : ℕ) (i : Fin (a.n k)) : Measurable (a.θ k i) :=
  measurable_normalizeLine ..

lemma Φ_measurable (k : ℕ) (i : Fin (a.n k)) : Measurable (a.Φ k i) := by
  unfold Φ
  exact ((a.θ_measurable k i).comp measurable_fst).prodMk (by fun_prop)

lemma prior_pos (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (a.n k)) :
    0 < (ν p (a.φ k) (a.γ k i) (a.A k i)).toReal := by
  have hN : 2 ≤ N p (a.φ k) := hp.1.1 _
  exact (Real.rpow_pos_of_pos (by linarith) _).trans_le (a.prior_lower k i)

lemma selected_law (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (a.n k)) :
    ((a.prior k i).prod volume).restrict (a.event k i) =
      (ENNReal.ofReal (a.dt k) * ν p (a.φ k) (a.γ k i) (a.A k i))⁻¹ •
        (mu p (a.φ k) (a.γ k i) |>.restrict (a.C k i)).map (a.Φ k i) := by
  let : IsProbabilityMeasure (ν p (a.φ k) (a.γ k i)) := ((hp.2 (a.φ k)).2.2.2.1 _).1
  have hdata := (a.data k).2.2.2.2.2.1 i
  exact chart_selected_transport _ _ _ _ ((a.data k).2.2.1 i).2
    (fun z hz => ⟨(a.selected_subset k i hz).1, mem_univ _⟩)
    (fun z hz => ((a.data k).2.2.2.2.1 i hz).1)
    (a.P k i) hdata.2.2.2.2.2.1 (a.t₀ k i) (a.dt k) (a.u k i) (a.v k i)
    (a.J k i) (a.δ k) (a.dt_pos k) hdata.2.1.ne' (a.δ_pos hp k).ne'

lemma selected_univ (hp : Spec.RawScalar p) (k : ℕ) (i : Fin (a.n k)) :
    (((a.prior k i).prod volume).restrict (a.event k i)) univ =
      (ENNReal.ofReal (a.dt k) * ν p (a.φ k) (a.γ k i) (a.A k i))⁻¹ *
        mu p (a.φ k) (a.γ k i) (a.C k i) := by
  rw [a.selected_law hp k i, Measure.smul_apply,
    Measure.map_apply (a.Φ_measurable k i) MeasurableSet.univ]
  simp

lemma selected_success (hp : Spec.RawScalar p) (M' D' : ℕ) (d' : ℝ) (k : ℕ) :
    ENNReal.ofReal ((8 * N p (a.φ k) ^ a.ε k)⁻¹) ≤
      ∑ i, ENNReal.ofReal (a.weight k i) * mu (a.code M' D' d') k i univ := by
  have hN : 2 ≤ N p (a.φ k) := hp.1.1 _
  have hN0 : 0 < N p (a.φ k) := by linarith
  have hden : ∀ i, ENNReal.ofReal
      (a.dt k * (ν p (a.φ k) (a.γ k i) (a.A k i)).toReal) =
      ENNReal.ofReal (a.dt k) * ν p (a.φ k) (a.γ k i) (a.A k i) := by
    intro i
    let : IsProbabilityMeasure (ν p (a.φ k) (a.γ k i)) := ((hp.2 (a.φ k)).2.2.2.1 _).1
    rw [ENNReal.ofReal_mul (a.dt_pos k).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hmass := ((a.data k).2.2.2.2.2.2.2.2.2).trans
    (weighted_union_le_sum (mu p (a.φ k)) (fun g => ENNReal.ofReal (ω p (a.φ k) g))
      (a.γ k) (a.C k))
  have hnorm := normalized_selected_mixture_lower_bound
    (fun i => ω p (a.φ k) (a.γ k i))
    (fun i => a.dt k * (ν p (a.φ k) (a.γ k i) (a.A k i)).toReal)
    (fun i => mu p (a.φ k) (a.γ k i) (a.C k i)) (a.Z k)
    (fun i => (hp.2 (a.φ k)).2.1 _) (fun i => mul_pos (a.dt_pos k) (a.prior_pos hp k i))
    (a.Z_pos hp k) (a.Z_le_one hp k) hmass
  have hstart : (8 * N p (a.φ k) ^ a.ε k)⁻¹ ≤ N p (a.φ k) ^ (-a.ε k) := by
    rw [Real.rpow_neg hN0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hN0 _)
    nlinarith [Real.rpow_pos_of_pos hN0 (a.ε k)]
  apply (ENNReal.ofReal_le_ofReal hstart).trans
  convert hnorm using 1
  apply Finset.sum_congr rfl
  intro i _
  change ENNReal.ofReal (a.budget k i / a.Z k) *
      (((a.prior k i).prod volume).restrict (a.event k i)) univ = _
  rw [a.selected_univ hp k i, hden]
  simp only [budget, mul_assoc]

lemma world_data (hp : Spec.RawScalar p) (hr : 0 ≤ r)
    {M' D' : ℕ}
    (hMcount : max (M p : ℝ) (a.B : ℝ) + 1 ≤ (M' : ℝ)) (hMfit : (4 : ℝ) ≤ M')
    (hMheight : (M p : ℝ) + 4 * h + 6 + ((a.B : ℝ) + 2) ≤ M')
    (hD : 2 * max (D p) a.B ≤ D') (k : ℕ) (i : Fin (a.n k)) :
    k4_scalar_conditional_crop_worlds.WorldData (N p (a.φ k) ^ (M' : ℝ)) D'
      (8 * N p (a.φ k) ^ a.ε k) (a.prior k i) (a.event k i) := by
  exact chart_normalized_world hp hr (a.ε_le_one k) hMcount hMfit hMheight hD
    (a.data k) (a.prior_lower k) i

theorem code_raw (hp : Spec.RawScalar p) {d' : ℝ} (hr : 0 ≤ r) (hrL : r < L p)
    (hd'0 : 0 ≤ d') (hd'1 : d' < 1) {M' D' : ℕ}
    (hMcount : max (M p : ℝ) (a.B : ℝ) + 1 ≤ (M' : ℝ)) (hMfit : (4 : ℝ) ≤ M')
    (hMheight : (M p : ℝ) + 4 * h + 6 + ((a.B : ℝ) + 2) ≤ M')
    (hD : 2 * max (D p) a.B ≤ D') (hD' : 1 ≤ D') :
    Spec.RawScalar (a.code M' D' d') := by
  obtain ⟨hN, hNt, _, _, _, hL, _, _, hS, hU⟩ := hp.1
  have hsub := normalization_loss_subpower (fun k => N p (a.φ k)) a.ε
    (fun k => hN _) (hNt.comp a.φ_mono.tendsto_atTop) (fun k => (a.ε_pos k).le) a.ε_lim
  refine ⟨⟨(fun k => hN _), hNt.comp a.φ_mono.tendsto_atTop, hsub, ?_, hD',
    sub_pos.mpr hrL, hd'0, hd'1, hS, div_pos (mul_pos hU (sub_pos.mpr hrL)) hL⟩, ?_⟩
  · have : (1 : ℝ) ≤ M' := by linarith
    exact_mod_cast this
  · intro k
    refine ⟨?_, (a.weights_probability hp k).1, (a.weights_probability hp k).2, ?_,
      a.selected_success hp M' D' d' k⟩
    · exact (a.data k).2.1.trans (Real.rpow_le_rpow_of_exponent_le
        (by have hh : 2 ≤ N p (a.φ k) := hN _; linarith)
        (by change (a.B : ℝ) ≤ (M' : ℝ); linarith [le_max_right (M p : ℝ) (a.B : ℝ)]))
    · intro i
      exact a.world_data hp hr hMcount hMfit hMheight hD k i

end ChosenCharts

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
