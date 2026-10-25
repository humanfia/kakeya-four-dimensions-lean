import Submission.Obl.k4_clean_cover_graph_atlas.SampleCaps
import Submission.Obl.k4_clean_cover_graph_atlas.PathBudgets
import Submission.Obl.k4_clean_cover_graph_atlas.ProjectionFloors
import Submission.Obl.k4_clean_cover_graph_atlas.PacketBounds

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}

/-- Original cap and mass control before subdivision. The profile and Jacobian
cancel against the original old prior, uniformly over every candidate. -/
theorem sampleInput_original_packet_control (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    (a : Fin n) :
    let fitExponent := 4 * ρ * gain * L + 4 * ε
    let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
    let H := 32 * Nk ^ (-f q + τ + 2 * fitExponent) * (|(Q (old a)).det| / (2 : ℝ) ^ T i)
    let frac := Nk ^ (-loss) / (64 * κ)
    let S := 8 * (κ + 1)
    let μ := ((ν (γ (old a))).prod volume).restrict (V a)
    0 < H ∧ 0 < frac ∧ frac ≤ 1 ∧ 1 ≤ S ∧
      μ.map (fun p => normBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) p.1 p.2) ≤
        ENNReal.ofReal H • volume ∧
      ENNReal.ofReal (H * frac) ≤ μ univ ∧
      (∀ᵐ p ∂μ, ‖normBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) p.1 p.2‖ ≤ S / 8) := by
  let fitExponent := 4 * ρ * gain * L + 4 * ε
  let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
  let H := 32 * Nk ^ (-f q + τ + 2 * fitExponent) * (|(Q (old a)).det| / (2 : ℝ) ^ T i)
  let frac := Nk ^ (-loss) / (64 * κ)
  let S := 8 * (κ + 1)
  let μ := ((ν (γ (old a))).prod volume).restrict (V a)
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hsi_saved := hsi
  obtain ⟨hscalar, hi, hgainh, _, _, hmargin, _, hentry, _, _, _, _, hq0, hqL, hqlo, hqhi⟩ := hsi
  obtain ⟨hlev, _, _, _, _, hA'A, _, _, hVm, hVsub, hfloor, _, _⟩ := hentry a
  have hchart := (hpath.2.2.2.2.2.2.2 (old a)).2.2
  rw [hlev] at hchart
  have hQ : (Q (old a)).det ≠ 0 := hchart.1
  have hJ : 0 < |(Q (old a)).det| := abs_pos.mpr hQ
  have hlen : 0 < (2 : ℝ) ^ T i := by positivity
  have hκ : 0 < κ := zero_lt_one.trans_le hpath.1
  have hfit : 0 ≤ fitExponent := by dsimp only [fitExponent]; positivity
  have hloss : 0 ≤ loss := by dsimp only [loss]; positivity
  have hU : 1 ≤ Nk ^ fitExponent := Real.one_le_rpow hNk hfit
  have hH : 0 < H := by dsimp only [H]; positivity
  obtain ⟨hfrac, hfrac1⟩ := projection_ratio_pos_le_one hNk hloss hpath.1
  refine ⟨hH, hfrac, hfrac1, by change 1 ≤ 8 * (κ + 1); linarith [hpath.1], ?_, ?_, ?_⟩
  · have hc := sampleInput_candidate_group_cap hNk hsi_saved a c u Q hQ 0
      (radius := 1) (by norm_num : (0 : ℝ) < 1) (cov := V a) Subset.rfl
    have heq : (groupBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) 0 1) ∘
        obs (B (γ (old a))) (δ Nk L) =
        fun p => normBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) p.1 p.2 := by
      funext p
      simp only [Function.comp_apply, groupBase, normBaseObs_obs, inv_one, sub_zero, one_smul]
    rw [heq] at hc
    simp only [one_pow, mul_one] at hc
    have hbins : 16 * (1 + (Nk ^ fitExponent) ^ 2) ≤ 32 * (Nk ^ fitExponent) ^ 2 := by nlinarith
    have hpow : Nk ^ (-f q + τ + 2 * fitExponent) = Nk ^ (-f q + τ) * (Nk ^ fitExponent) ^ 2 := by
      rw [show -f q + τ + 2 * fitExponent = (-f q + τ) + fitExponent + fitExponent by ring,
        Real.rpow_add hNkpos, Real.rpow_add hNkpos, pow_two]
      ring
    have hcoef : Nk ^ (-f q + τ) * (16 * (1 + (Nk ^ fitExponent) ^ 2)) * |(Q (old a)).det| /
        (2 : ℝ) ^ T i ≤ H := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbins (Real.rpow_nonneg hNkpos.le (-f q + τ)))
        (div_nonneg hJ.le hlen.le)
      dsimp only [H]
      rw [hpow]
      convert hh using 1 <;> ring
    apply hc.trans
    apply Measure.le_iff.mpr
    intro Z hZ
    simpa only [Measure.smul_apply, smul_eq_mul] using
      mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) (le_rfl : volume Z ≤ volume Z)
  · have hri : 0 < r i := (hpath.2.2.2.2.1 i hi).2.1
    have hh : 0 < h := hgain.trans_le hgainh
    have hriL : r i ≤ L := by nlinarith [mul_pos hh hL]
    have hprofile := (menuDepth_profile_increment hL.le hd₁ hd₁1 hδ₀ ⟨hri.le, hriL⟩ ⟨hq0, hqL⟩
      (fun z hz => hlin z hz.1 hz.2) hqlo hqhi).1
    have hprior := path_packet_prior_floor hNkpos hpath (old a) hlev
    letI := (hscalar.2.2.2 (γ (old a))).1
    have hfloor' : ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) /
        (2 * (2 : ℝ) ^ T i)) * ν (γ (old a)) (A (old a)) ≤
        ((ν (γ (old a))).prod volume) (V a) := by
      convert hfloor using 2
      congr 1
      ring
    have hm := original_candidate_projection_mass_floor (τ := τ) (ν (γ (old a))) (A (old a))
      (((ν (γ (old a))).prod volume) (V a)) (measure_ne_top _ _) hNk hJ.le hlen hκ
      hprior hprofile hfloor'
    simpa only [H, frac, loss, fitExponent, μ, Measure.restrict_apply_univ] using hm
  · apply ae_restrict_of_forall_mem hVm
    intro p hp
    have hp' := hVsub hp
    calc
      _ ≤ κ + 1 := normBase_bound_of_chart hchart (hA'A hp'.2.1) hp'.2.2.1
      _ = S / 8 := by change κ + 1 = (8 * (κ + 1)) / 8; ring

end
end Submission.Obl.k4_clean_cover_graph_atlas
