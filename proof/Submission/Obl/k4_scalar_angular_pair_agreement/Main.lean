import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.Scale
import Submission.Obl.k4_scalar_angular_pair_agreement.ChartGeometry
import Submission.Obl.k4_scalar_angular_pair_agreement.PowerBounds

/-!
# Assembly of `k4_scalar_angular_pair_agreement`

Constants: `a = 3 + 54 / S₀`, `c = η S₀ / 6`; for `e < c L` the angular depth `uu = 6e/S₀`
is at most `U = η L`, and the cap slack is `τ = e / 8`.  Given `σ > 0` we use old true charts
of tolerance `ε = min σ (min e c_cap) / 40`, which are also charts of tolerance `σ`, coarsen
to `T₁` with `2^(T - T₁) ≤ N^e`, and conclude from the fixed-scale inequality.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Chart systems are monotone in the time bound and the tolerance. -/
lemma chartData_mono {p : Code} {B : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool} {k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 1 ≤ N p k) (hh : h ≤ h') (he : ε ≤ ε')
    (hd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ChartData p B r b h' ε' isTrue k T n γ j A C u v J P Λ := by
  obtain ⟨hT, hn, hAC, hdisj, hCsub, hlab, hΛcard, hΛmeas, hΛae, hmass⟩ := hd
  have hNpos : 0 < N p k := lt_of_lt_of_le zero_lt_one hN
  have hεle : N p k ^ ε ≤ N p k ^ ε' := Real.rpow_le_rpow_of_exponent_le hN he
  have hε0 : 0 < N p k ^ ε := Real.rpow_pos_of_pos hNpos _
  refine ⟨hT.trans (Real.rpow_le_rpow_of_exponent_le hN hh), hn, hAC, hdisj, hCsub,
    fun i => ?_, fun a z => (hΛcard a z).trans hεle, hΛmeas, hΛae, ?_⟩
  · obtain ⟨hμ, hJ, hJinv, hJle, huv, hdeg, hcoef, hlb, hF5, hF6, hfit, hfloor⟩ := hlab i
    refine ⟨hμ, hJ, hJinv, hJle.trans (by gcongr), huv.trans hεle, hdeg, hcoef,
      fun l hl => ⟨(hlb l hl).1, fun e => ((hlb l hl).2 e).trans hεle⟩, hF5, hF6,
      fun l hl t ht => ⟨(hfit l hl t ht).1.trans (by gcongr), (hfit l hl t ht).2.trans
        (by gcongr)⟩, fun htrue => ?_⟩
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hfloor htrue)
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (Real.rpow_nonneg hNpos.le _) hJ.le
    · positivity
    · gcongr
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- A constant times a smaller power is at most a larger power, once the gap power exceeds
the constant. -/
lemma mul_rpow_neg_le {Nk C s t : ℝ} (hN : 0 < Nk) (hC : C ≤ Nk ^ (s - t)) :
    C * Nk ^ (-s) ≤ Nk ^ (-t) := by
  calc C * Nk ^ (-s) ≤ Nk ^ (s - t) * Nk ^ (-s) := by
        gcongr
    _ = Nk ^ (-t) := by rw [← Real.rpow_add hN]; ring_nf

/-- The explicit power left by the capped witnesses is at most `3564 N^(-2e)`. -/
lemma Kc_le {Nk e ε τ Su R : ℝ} (hN : 1 ≤ Nk) (he : 0 < e) (hε : 0 ≤ ε) (hεe : ε ≤ e / 40)
    (hSu : Su = 6 * e) (hτ : τ = e / 8) (hR1 : 1 ≤ R) (hR : R ≤ Nk ^ e) :
    12 * Nk ^ (-Su + τ) * (2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1) * Nk ^ ε * Nk ^ ε * Nk ^ ε *
      (1 + 2 * R) ≤ 3564 * Nk ^ (-(2 * e)) := by
  have hNpos : 0 < Nk := lt_of_lt_of_le zero_lt_one hN
  have hA : 1 ≤ Nk ^ ε := Real.one_le_rpow hN hε
  have hX : 1 ≤ Nk ^ e := Real.one_le_rpow hN he.le
  have hc : 0 < Nk ^ (-Su + τ) := Real.rpow_pos_of_pos hNpos _
  have h1 : 2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1 ≤ 99 * (Nk ^ e) ^ 2 * Nk ^ ε := by
    have : R ^ 2 ≤ (Nk ^ e) ^ 2 := by gcongr
    have h3 : (3 : ℝ) ≤ 3 * (Nk ^ e) ^ 2 * Nk ^ ε := by
      have : 1 ≤ (Nk ^ e) ^ 2 * Nk ^ ε := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) hA
      linarith
    nlinarith
  have h2 : 1 + 2 * R ≤ 3 * Nk ^ e := by linarith
  calc 12 * Nk ^ (-Su + τ) * (2 * (48 * R ^ 2 * Nk ^ ε + 1) + 1) * Nk ^ ε * Nk ^ ε * Nk ^ ε *
        (1 + 2 * R)
      ≤ 12 * Nk ^ (-Su + τ) * (99 * (Nk ^ e) ^ 2 * Nk ^ ε) * Nk ^ ε * Nk ^ ε * Nk ^ ε *
          (3 * Nk ^ e) := by gcongr
    _ = 3564 * (Nk ^ (-Su + τ) * Nk ^ e * Nk ^ e * Nk ^ e * Nk ^ ε * Nk ^ ε * Nk ^ ε *
          Nk ^ ε) := by ring
    _ = 3564 * Nk ^ (-Su + τ + e + e + e + ε + ε + ε + ε) := by
        simp only [Real.rpow_add hNpos]
    _ ≤ 3564 * Nk ^ (-(2 * e)) := by
        gcongr
        rw [hSu, hτ]; linarith

/-- The readable statement holds. -/
theorem main : Statement := by
  intro S₀ η hS₀ hη
  have h54 : 0 < 54 / S₀ := by positivity
  refine ⟨3 + 54 / S₀, η * S₀ / 6, by linarith, by positivity, ?_⟩
  intro p hp hSp hUp h e hh hCost he heh hec
  obtain ⟨⟨hN2, hNt, _, _, _, hL, _, _, _, _⟩, hworld, _, hρa, _, _, _, hcap⟩ := hp
  set uu : ℝ := 6 * e / S₀ with huu_def
  set τ : ℝ := e / 8 with hτ_def
  have huu : 0 < uu := by positivity
  have huuU : uu ≤ U p := by
    rw [hUp, huu_def, div_le_iff₀ hS₀]
    have : e < η * S₀ / 6 * L p := hec
    nlinarith
  have hSu : S p * uu = 6 * e := by rw [hSp, huu_def]; field_simp
  obtain ⟨ca, hca, hcapev⟩ := hcap uu τ huu huuU (by positivity)
  obtain ⟨_, B, hB, hchart⟩ := hCost
  refine ⟨B, hB, fun σ hσ => ?_⟩
  set ε : ℝ := min σ (min e ca) / 40 with hε_def
  have hε : 0 < ε := by positivity
  have hεσ : ε ≤ σ / 40 := by
    rw [hε_def]; gcongr; exact min_le_left _ _
  have hεe : ε ≤ e / 40 := by
    rw [hε_def]; gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεc : ε ≤ ca / 40 := by
    rw [hε_def]; gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
  have hfreq := hchart ε hε
  have hev : ∀ᶠ k in atTop,
      (∑ w, ENNReal.ofReal (ω p k w) * mu p k w (Exc p k w uu τ) ≤
        ENNReal.ofReal (N p k ^ (-ca))) ∧
      geometryConstant ≤ N p k ^ (e / 2) ∧
      (3 : ℝ) ≤ N p k ^ (σ - 2 * ε) ∧ (3 : ℝ) ≤ N p k ^ (ca - 2 * ε) ∧
      (3 * 3564 : ℝ) ≤ N p k ^ (2 * e - 2 * ε) := by
    refine hcapev.and ((eventually_geometry_constant_le hNt he).and
      ((Submission.Obl.k4_scalar_terminal_chart_packet_extraction.eventually_const_le_rpow
        hNt 3 (by linarith)).and
      ((Submission.Obl.k4_scalar_terminal_chart_packet_extraction.eventually_const_le_rpow
        hNt 3 (by linarith)).and
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.eventually_const_le_rpow
        hNt (3 * 3564) (by linarith)))))
  refine (hfreq.and_eventually hev).mono ?_
  rintro k ⟨⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩, hcapk, hgeo, h3σ, h3c, h3e⟩
  have hN1 : 1 ≤ N p k := by linarith [hN2 k]
  have hNpos : 0 < N p k := by linarith [hN2 k]
  refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ,
    chartData_mono hN1 (by linarith) (by linarith) hcd, ?_⟩
  have hX : 1 ≤ N p k ^ e := Real.one_le_rpow hN1 he.le
  obtain ⟨T₁, hT₁, hRX, hT₁X⟩ := exists_T₁ T hX
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ (T - T₁) := one_le_pow₀ (by norm_num)
  refine ⟨T₁, hT₁, by linarith, ?_, ?_⟩
  · rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv]; exact hT₁X
  -- the bins of bad label pairs
  have hw : 0 < N p k ^ (-uu) := Real.rpow_pos_of_pos hNpos _
  have hw1 : N p k ^ (-uu) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hnum := geometry_power_bound (L := L p) (u := uu) (a := 3 + 54 / S₀) (θ := ε)
    hN1 he.le (by positivity) (hRX.trans (by linarith)) hεe
    (by rw [huu_def]; field_simp; ring_nf; rfl) hgeo
  have hex : ∀ (b : Fin (2 ^ T₁)) (i i' : Fin n), ∃ F : Finset ℤ,
      I T (j i) ⊆ I T₁ b → I T (j i') ⊆ I T₁ b →
      ¬ Agrees p k T₁ n u v P (3 + 54 / S₀) e b i i' →
      F.card ≤ 6 ∧ ∀ l ∈ A i ∩ A i', ⌊l.2 1 / N p k ^ (-uu)⌋ ∈ F := by
    intro b i i'
    by_cases hc : I T (j i) ⊆ I T₁ b ∧ I T (j i') ⊆ I T₁ b ∧
        ¬ Agrees p k T₁ n u v P (3 + 54 / S₀) e b i i'
    · obtain ⟨F, hF1, hF2⟩ := bad_chart_common_velocity_bins hcd hN1 hε.le hT₁ b i i'
        hc.1 hc.2.1 hw hw1 hnum hc.2.2
      exact ⟨F, fun _ _ _ => ⟨hF1, fun l hl => hF2 l hl.1 hl.2⟩⟩
    · exact ⟨∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
  choose Fb hFb using hex
  -- the fixed-scale inequality
  have hfs := fixed_scale_bound (τ := τ) hNpos (fun w => ((hworld k).2.1 w)) (hworld k).2.2.1
    (fun w => ((hworld k).2.2.2.1 w).1) hcd hT₁ (fun w => (hρa k w uu huu huuU).1)
    (fun w => (hρa k w uu huu huuU).2) Fb
    (fun w b i i' hi hi' hbad => hFb b i i' (mem_Sblk.mp hi).2 (mem_Sblk.mp hi').2 hbad)
  -- numerics
  have hKc := Kc_le hN1 he hε.le hεe hSu hτ_def hR1 hRX
  set Kc : ℝ := 12 * N p k ^ (-(S p * uu) + τ) *
    (2 * (48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * N p k ^ ε + 1) + 1) *
    N p k ^ ε * N p k ^ ε * N p k ^ ε * (1 + 2 * (2 : ℝ) ^ (T - T₁)) with hKc_def
  have hsq : ENNReal.ofReal (N p k ^ (-ε)) ^ 2 = ENNReal.ofReal (N p k ^ (-(2 * ε))) := by
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hNpos.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul hNpos.le]
    congr 2; push_cast; ring
  have hreal : N p k ^ (-σ) + N p k ^ (-ca) + Kc ≤ N p k ^ (-(2 * ε)) := by
    have e1 : 3 * N p k ^ (-σ) ≤ N p k ^ (-(2 * ε)) := mul_rpow_neg_le hNpos h3σ
    have e2 : 3 * N p k ^ (-ca) ≤ N p k ^ (-(2 * ε)) := mul_rpow_neg_le hNpos h3c
    have e3 : (3 * 3564) * N p k ^ (-(2 * e)) ≤ N p k ^ (-(2 * ε)) :=
      mul_rpow_neg_le hNpos h3e
    linarith
  have hKc0 : 0 ≤ Kc := by positivity
  rw [hsq] at hfs
  have hlhs : ENNReal.ofReal (N p k ^ (-σ)) +
      (ENNReal.ofReal (N p k ^ (-ca)) + ENNReal.ofReal Kc) ≤
      ENNReal.ofReal (N p k ^ (-(2 * ε))) := by
    rw [← ENNReal.ofReal_add (by positivity) hKc0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hfin : ENNReal.ofReal (N p k ^ (-ca)) + ENNReal.ofReal Kc ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  refine (ENNReal.add_le_add_iff_right hfin).mp ?_
  calc ENNReal.ofReal (N p k ^ (-σ)) + (ENNReal.ofReal (N p k ^ (-ca)) + ENNReal.ofReal Kc)
      ≤ ENNReal.ofReal (N p k ^ (-(2 * ε))) := hlhs
    _ ≤ pairMass p k T n γ j C u v P (3 + 54 / S₀) e T₁ +
        ∑ w, ENNReal.ofReal (ω p k w) * mu p k w (Exc p k w uu τ) + ENNReal.ofReal Kc := hfs
    _ ≤ pairMass p k T n γ j C u v P (3 + 54 / S₀) e T₁ +
        (ENNReal.ofReal (N p k ^ (-ca)) + ENNReal.ofReal Kc) := by
        rw [add_assoc]; gcongr

end Submission.Obl.k4_scalar_angular_pair_agreement
