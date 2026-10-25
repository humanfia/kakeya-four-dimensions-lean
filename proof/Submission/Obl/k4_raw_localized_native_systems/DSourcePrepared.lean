import Submission.Obl.k4_raw_localized_native_systems.DSource
import Submission.Obl.k4_raw_localized_native_systems.DSourceNumerics
import Submission.Obl.k4_raw_localized_native_systems.C.SourceFrameAncestry

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests
open Window Pairing Packing

noncomputable section
set_option maxHeartbeats 2000000

/-- A prepared homogeneous pair of actual source layers supplies the finite
certificate callback. All deletions are measured under the original worlds. -/
theorem source_d_step {p : Data} (hp : Valid p) (hL : p.L = 1) {k M D : ℕ}
    {r : ℕ → ℝ} (a : Forest p k) (ha : a.Core M D 2 r)
    (hprep : a.Prepared r (sourceLists a r))
    {χ ds s τ band u K loss g a₀ nw : ℝ}
    (hχ : 0 < χ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r 0) (hrL : r 0 ≤ p.L) (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hband : 0 ≤ band) (hup : 8 * u + 2 * band ≤ 1) (hloss : loss ≤ 4)
    (hnum : RawSampleBounds (p.N k) a.κ K χ τ (r 0) s band (8 * u + 2 * band))
    (hcurrentK : p.N k ^ loss ≤ K)
    (hprofile : p.f (r 0) - p.f 0 + τ + 4 * band + 2 * (8 * u + 2 * band) + χ / 2 ≤
      ds * s + χ)
    (hT : (2 : ℝ) ^ a.T 0 ≤ p.N k)
    (width : Fin a.C → ℝ)
    (hexact : ∀ b, a.lev b = 0 → p.N k ^ (-width b) = |(a.Q b).det| * (4 : ℝ) ^ a.T 0)
    (hwidth : ∀ b, a.lev b = 0 → |width b - nw| ≤ band)
    (hpinSmall : 16 * a.κ * p.N k ^ (-4 * u) ≤ δ (p.N k) u)
    (hsmall : 10 * (∑ γ, ENNReal.ofReal (p.ω k γ) *
        selected p k γ (densityGood p {0, r 0} {u} τ k γ)ᶜ) +
      2 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
        (shortWitnessEvent (sourceFrame a ha 0)
          ((1 / (2 : ℝ) ^ a.T 0) * p.N k ^ (-(4 * u))) γ)) < ENNReal.ofReal a.κ⁻¹)
    (homit : 6 * (∑ γ, ENNReal.ofReal (p.ω k γ) *
        selected p k γ (densityGood p {0, r 0} {u} τ k γ)ᶜ) +
      (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
        (shortWitnessEvent (sourceFrame a ha 0)
          ((1 / (2 : ℝ) ^ a.T 0) * p.N k ^ (-(4 * u))) γ)) +
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
        ((9 * ⌈p.N k ^ loss⌉₊ * ⌈a.κ⌉₊ + 9 * ⌈a.κ⌉₊ : ℕ) : ENNReal) ≤
          ENNReal.ofReal (p.N k ^ (-a₀)))
    (hg : 0 < g)
    (hrel : ∀ b : Fin a.C, a.lev b = 0 →
      g ≤ p.N k ^ (-4 : ℝ) * C.minorWidth (a.Q b) / (2 : ℝ) ^ a.T 0)
    (MC DC : ℕ)
    (Λ : Fin (p.W k) → Observation → Finset (Fin (C.levelSet a 1).card)) :
    C.DStep RawSupport p k (C.levelAtlas a 1 Λ) MC DC loss g a₀ χ ds s (s + 4) := by
  let W := sourceFrame a ha 0
  let Good := densityGood p {0, r 0} {u} τ k
  let q := 1 / (2 : ℝ) ^ W.T
  let g₁ := p.N k ^ (-nw - band)
  let lam := q * p.N k ^ (-(4 * u))
  let S := longHeavyWitnessSet W Good lam
  let V := selectWitnesses W S
  let U := sourceLayer a ha 0
  let lst₁ := (selectWitnesses U S).lst
  have hκ : 1 ≤ a.κ := ha.1
  have hκ0 : 0 < a.κ := by linarith
  have hN := hp.scale_ge_one k
  have hN0 := hp.scale_pos k
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    calc
      _ ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by norm_num)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      _ = _ := one_div_one
  have hg₁ : 0 < g₁ := Real.rpow_pos_of_pos hN0 _
  have hW : ∀ e, WChart p k W M D a.κ (r 0) e :=
    sourceFrame_wchart hp a ha hprep (by omega) hrL
  have hWfloor := sourceFrame_floor a ha (i := 0) (by omega)
  have hdisj := sourceFrame_disjoint a ha (i := 0) (by omega)
  have hGood : ∀ γ, MeasurableSet (Good γ) := by
    apply measurableSet_densityGood hp
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨le_rfl, by rw [hL]; norm_num⟩
      · exact ⟨hr0, hrL⟩
    · intro z hz
      have hz' : z = u := Finset.mem_singleton.mp hz
      subst z
      exact ⟨hu, huη⟩
  have hnonempty : Nonempty (Fin S.card) :=
    long_heavy_witness_nonempty hp W hW hdisj Good hGood lam
      (hsmall.trans_le (sourceFrame_coverage a ha (i := 0) (by omega)))
  have hrelW := C.source_frame_relative_width a ha 0 hN0 hrel
  have hWexact (e : Fin W.C) : p.N k ^ (-width (a.layerEmb 0 e)) =
      |(W.Q e).det| * (4 : ℝ) ^ W.T := hexact _ (a.layerEmb_lev _ _)
  have hWwidth (e : Fin W.C) : |width (a.layerEmb 0 e) - nw| ≤ band :=
    hwidth _ (a.layerEmb_lev _ _)
  have hminor (e : Fin V.C) : minorWidth (V.Q e) ≤ q * g₁ * p.N k ^ (2 * band + 4 * u) :=
    minor_width_power_bound hN hq hg₁.le
      (determinant_band_bounds hN rfl (hWexact (witnessIndex S e))
        (hWwidth (witnessIndex S e))).2
      (long_heavy_witness_major W Good lam e)
  have hcurrent : g ≤ q ^ 2 * g₁ * p.N k ^ (2 * band + 4 * u) / p.N k ^ (4 : ℕ) := by
    let e := Classical.choice hnonempty
    apply relative_width_long_upper hN hq hg₁.le
      (determinant_band_bounds hN rfl (hWexact (witnessIndex S e))
        (hWwidth (witnessIndex S e))).2
      (long_heavy_witness_major W Good lam e)
    convert hrelW (witnessIndex S e) using 1
    dsimp only [q, V, selectWitnesses]
    field_simp
    ring
  have hσ : ∀ e : Fin V.C, minorWidth (V.Q e) * (2 * a.κ * (2 : ℝ) ^ W.T) ≤
      2 * a.κ * g₁ * p.N k ^ (2 * band + 4 * u) := by
    intro e
    have hh := mul_le_mul_of_nonneg_left (hminor e)
      (show 0 ≤ 2 * a.κ / q by positivity)
    convert hh using 1 <;> dsimp only [q] <;> field_simp <;> ring
  have hpin := long_scale_pinning hN hκ hq hq1 hg₁ hloss hcurrent hpinSmall
  have hshort : 4 * a.κ * (2 : ℝ) ^ W.T * lam ≤ δ (p.N k) u := by
    have hh := long_scale_short hN0.le hq.ne' hκ0.le hpinSmall
    convert hh using 1
    dsimp only [lam, q]
    simp only [neg_mul]
    field_simp
  have hcard₁ (γ : Fin (p.W k)) (o : Observation) : (lst₁ γ o).card ≤ ⌈a.κ⌉₊ := by
    have hh := (Nat.cast_le.mpr (selected_witness_list_card U S γ o)).trans
      (sourceFrame_own_card a ha hprep 0 γ o)
    exact_mod_cast hh.trans (Nat.le_ceil a.κ)
  have hmeas₁ : ∀ γ e, MeasurableSet {o | e ∈ lst₁ γ o} :=
    selected_witness_list_measurable U S (sourceLayer_lists_measurable a ha 0)
  have hknown₁ : ∀ e z, z ∈ V.F e →
      e ∈ lst₁ (V.γ e) (obs (p.B k (V.γ e)) (δ (p.N k) (r 0)) z) := by
    intro e z hz
    apply (selected_witness_mem_list U S _ _ e).mpr
    exact sourceFrame_own_known a ha hprep 0 (witnessIndex S e) z hz
  have hwindow : p.N k ^ (-(s + 4)) ≤ q := by
    rw [Real.rpow_neg hN0.le]
    calc
      _ ≤ (p.N k)⁻¹ := (inv_le_inv₀ (by positivity) hN0).mpr
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hN (show (1 : ℝ) ≤ s + 4 by linarith))
      _ ≤ q := by
        dsimp only [q]
        rw [one_div]
        exact (inv_le_inv₀ hN0 (by positivity)).mpr hT
  intro CC γC nC int sp AC FC lstC hfam
  apply finite_d_step hp hL hχ hnum.chiPower hnum.largeScale hs1 hκ hnum.sourceCover
    hnum.packingPositive hnum.packingQuadratic hnum.packingScale
    (ha.2.1.trans (by linarith only [hnum.sourceCover, hκ])) hr0 hrL
    W hW hWfloor Good hGood hnonempty ?_ ?_ ?_ ?_ hdisj hnum.densityBudget hnum.scalarBudget
    (ha.2.1.trans (by linarith only [hnum.scalarBudget, hκ])) hnum.valueBudget hnum.curvatureBudget
    hT rfl hband (by positivity) hup (by linarith) ?_ hnum.errorBudget hnum.angleBudget hwindow
    hnum.polynomialBudget hprofile (sourceFrame_known hp a ha hprep (by omega) hrL)
    (fun γ o => (sourceFrame_card hp a ha hprep (by omega) hrL γ o).trans
      (by linarith only [hnum.sourceCover, hκ]))
    (fun e => width (a.layerEmb 0 e)) hWexact hWwidth lst₁ ⌈a.κ⌉₊ hcard₁ hmeas₁ hknown₁
    hu huη (by positivity) hσ hpin hshort homit hg hcurrentK hrelW
    (C.levelAtlas a 1 Λ) γC nC int sp AC FC lstC hfam
    (fun c z hz => hfam.source_frame_ancestry a ha 0 Λ c hz)
  · intro γ z hz
    exact (densityGood_pure hz (by simp)).2
  · intro γ z hz
    simpa only [delta_zero] using (densityGood_pure hz (r := 0) (by simp)).2
  · intro γ z hz
    exact (densityGood_speed hz).trans (ha.2.1.trans (by linarith only [hnum.sourceCover, hκ]))
  · intro γ z hz
    exact densityGood_angGood hz (by simp)
  · have hh : 0 ≤ g₁ * p.N k ^ (8 * u + 2 * band) := by positivity
    dsimp only [g₁] at hh ⊢
    nlinarith only [hh]

end
end Submission.Obl.k4_raw_localized_native_systems
