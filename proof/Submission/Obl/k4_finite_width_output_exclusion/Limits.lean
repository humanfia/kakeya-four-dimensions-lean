import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport
import Submission.Obl.k4_finite_width_output_exclusion.Subsequence

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma delta_compare {N r s e : ℝ} (hN : 1 ≤ N) (hrs : |r - s| ≤ e) :
    δ N r ≤ 2 * N ^ e * δ N s := by
  have hNpos : 0 < N := by linarith
  have hb := (abs_le.1 hrs).1
  calc
    δ N r ≤ 2 * N ^ (-r) := (delta_bounds hNpos r).2
    _ ≤ 2 * N ^ (e - s) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
      norm_num
    _ = 2 * N ^ e * N ^ (-s) := by rw [sub_eq_add_neg, Real.rpow_add hNpos]; ring
    _ ≤ 2 * N ^ e * δ N s :=
      mul_le_mul_of_nonneg_left (delta_bounds hNpos s).1 (by positivity)

lemma delta_with_slack {N r s τ ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hτ : τ ≤ ε / 4) (hrs : |r - s| ≤ ε / 4) (h2 : 2 ≤ N ^ (ε / 2)) :
    N ^ τ * δ N r ≤ N ^ ε * δ N s := by
  have hNpos : 0 < N := by linarith
  calc
    N ^ τ * δ N r ≤ N ^ τ * (2 * N ^ (ε / 4) * δ N s) :=
      mul_le_mul_of_nonneg_left (delta_compare hN hrs) (by positivity)
    _ = 2 * N ^ (τ + ε / 4) * δ N s := by rw [Real.rpow_add hNpos]; ring
    _ ≤ N ^ (ε / 2) * N ^ (ε / 2) * δ N s := by
      apply mul_le_mul_of_nonneg_right ?_ (delta_pos N s).le
      exact mul_le_mul h2 (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
        (by positivity) (by positivity)
    _ = N ^ ε * δ N s := by rw [← Real.rpow_add hNpos]; congr 2; ring

lemma known_of_convergent {p : Data} (hp : Valid p) {M D : ℕ}
    {r τ : ℕ → ℝ} {r₀ h w : ℝ}
    (hr : Tendsto r atTop (nhds r₀)) (hτ : Tendsto τ atTop (nhds 0))
    (hsamples : ∀ k : ℕ, ∃ a : Atlas p k,
      (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧
      (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + 2 * τ k)) ∧
      a.KnownAt M D (p.N k ^ τ k) (r k)) : Known p r₀ h w := by
  refine ⟨M, D, fun ε hε => ?_⟩
  have htau : ∀ᶠ k in atTop, τ k ≤ ε / 4 :=
    (hτ.eventually (gt_mem_nhds (show 0 < ε / 4 by positivity))).mono (fun _ hk => hk.le)
  have hdepth : ∀ᶠ k in atTop, |r k - r₀| ≤ ε / 4 := by
    have h := hr.eventually (Metric.ball_mem_nhds r₀ (show 0 < ε / 4 by positivity))
    simpa only [Metric.mem_ball, Real.dist_eq] using h.mono (fun _ hk => hk.le)
  have htwo : ∀ᶠ k in atTop, 2 ≤ p.N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp hp.scale_tendsto).eventually
      (eventually_ge_atTop 2)
  apply (htau.and (hdepth.and htwo)).frequently.mono
  rintro k ⟨ht, hd, h2⟩
  obtain ⟨a, hT, hw, ⟨hC, hdisj, hchart, hmass⟩, hlst⟩ := hsamples k
  have hκ : 0 < p.N k ^ τ k := Real.rpow_pos_of_pos (hp.scale_pos k) _
  have hκκ : p.N k ^ τ k ≤ p.N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)
  refine ⟨p.N k ^ ε, Real.one_le_rpow (hp.scale_ge_one k) hε.le, le_rfl, a,
    hT.trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)),
    fun b => (hw b).trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)),
    ⟨hC, hdisj, ?_, ?_⟩, fun γ o => (hlst γ o).trans hκκ⟩
  · intro b
    apply chart_transport le_rfl hκ hκκ (hp.B_pos k (a.γ b)).le
      (delta_with_slack (hp.scale_ge_one k) hε ht hd h2) ?_ id (hchart b)
    apply (div_le_div_iff₀ (delta_pos (p.N k) (r k)) (delta_pos (p.N k) r₀)).2
    exact delta_with_slack (hp.scale_ge_one k) hε ht (by simpa only [abs_sub_comm] using hd) h2
  · apply le_trans (b := ENNReal.ofReal ((p.N k ^ τ k)⁻¹)) ?_ hmass
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ hκ hκκ)

end
end Submission.Obl.k4_finite_width_output_exclusion
