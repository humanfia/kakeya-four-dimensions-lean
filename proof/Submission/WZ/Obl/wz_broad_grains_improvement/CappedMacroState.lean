-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedMacroState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedThinUniform
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismState
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedReframe
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData capped_parameter_cell capped_axial_reframe G_iff_data G_scales)
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine (exists_power_absorption)

/-- A capped family of thin, short prisms at macroscopic coarse radius gives
a gain or a full original-indexed grain state at radius one. -/
theorem macroscopic_capped_prisms_gain_or_state {σ ω ζ ε τ u : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hε : 0 < ε) (hτ : 0 < τ) (hu : 0 < u)
    (hβ : 0 ≤ ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1) :
    ∃ α κ η t d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < t ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      d^t ≤ ρ → c ≤ d^u → 4*d ≤ c → D.a ≤ d^τ*c →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        J ω ζ d ε 1 (8388608*c) n x v Y 0 := by
  obtain ⟨ηJ,dJ,hηJ,hηJε,hdJ,hdJ100,HJ⟩ :=
    stage_zero_of_capped_prisms (ω := ω) (ζ := ζ) hε
  let e := min ηJ (min 1 (20*τ))
  have he : 0 < e := by dsimp [e]; positivity
  have heJ : e ≤ ηJ := min_le_left _ _
  have he1 : e ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have heτ : e ≤ 20*τ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨κ,r,dT,hκ,hr,hre,hdT,hdT100,HT⟩ :=
    thin_prisms_gain_or_capped_stage_two hσ hσ2 hω hω1 hE he he1 hβ
  let θ : ℝ := 1/16384
  let K : ℝ := 262144
  have hθ : 0 < θ := by norm_num [θ]
  have hK : 0 < K := by norm_num [K]
  obtain ⟨q,hq,Hcell⟩ := capped_parameter_cell hθ
  let a₁ := r/3
  let a₂ := 2*r/3
  let t := r/12
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨dE,hdE,HE⟩ := exists_power_absorption
    (C := 4608*(100*K+2)) (p := u) (r := u/2) (by positivity) (by linarith)
  obtain ⟨dM,hdM,HM⟩ := exists_power_absorption
    (C := 4/q) (p := a₁) (r := r/12) (by positivity) (by dsimp [a₁]; linarith)
  obtain ⟨dB,hdB,HB⟩ := exists_power_absorption
    (C := 2/q) (p := -a₁) (r := -a₂) (by positivity) (by dsimp [a₁,a₂]; linarith)
  obtain ⟨dV,hdV,HV⟩ := exists_power_absorption
    (C := 128*K^3*θ) (p := r) (r := a₂+t) (by positivity) (by dsimp [a₂,t]; linarith)
  obtain ⟨dA,hdA,HA⟩ := exists_power_absorption
    (C := 2097152) (p := τ) (r := e/100) (by norm_num) (by linarith)
  obtain ⟨dC,hdC,HC⟩ := exists_power_absorption
    (C := 1048576*K) (p := u) (r := 0) (by positivity) hu
  refine ⟨(e/100)*ω/2,κ,min (r/12) (u/4),t,
    min dJ (min dT (min (θ/8) (min dE (min dM (min dB (min dV (min dA dC))))))),
    by positivity,hκ,by positivity,(min_le_left _ _).trans
      ((show r/12 ≤ r by linarith).trans (hre.trans (heJ.trans hηJε))),
    ht,by positivity,(min_le_left _ _).trans hdJ100,?_⟩
  intro d h n x v Y hd hdd hh hA ρ c D HD Hcaps hρlo hcu hdc hthin
  have hcuts : d≤dJ ∧ d≤dT ∧ d≤θ/8 ∧ d≤dE ∧ d≤dM ∧ d≤dB ∧ d≤dV ∧ d≤dA ∧ d≤dC := by
    simpa only [le_min_iff] using hdd
  obtain ⟨hdJ',hdT',hdθ,hdE',hdM',hdB',hdV',hdA',hdC'⟩ := hcuts
  have hd1 : d ≤ 1 := (hdJ'.trans hdJ100).trans (by norm_num)
  have hh₁₂ : h ≤ r/12 := hh.trans (min_le_left _ _)
  have hhu : h ≤ u/4 := hh.trans (min_le_right _ _)
  have hhr : h ≤ r := by linarith
  obtain ⟨_,hρ,hρ1,_,hc,_⟩ := G_scales hd (G_iff_data.mpr ⟨D,HD⟩)
  have hsmall : K*c ≤ 1/1048576 := by
    have hb := HC d hd hdC'
    rw [Real.rpow_zero] at hb
    have hh' := mul_le_mul_of_nonneg_left hcu (by positivity : 0≤1048576*K)
    nlinarith
  have hthinpower : 128*d^τ ≤ θ*d^(e/100) := by
    have hb := HA d hd hdA'
    dsimp [θ]
    linarith
  have hthinold : D.a ≤ θ*c/128 := by
    have heone : d^(e/100) ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity)
    have hp := mul_le_mul_of_nonneg_right hthinpower hc.le
    have hq' := mul_le_mul_of_nonneg_left heone (mul_nonneg hθ.le hc.le)
    nlinarith [hthin]
  have hthinnew : 128*K*D.a ≤ d^(e/100)*(θ*(K*c)) := by
    have hp := mul_le_mul_of_nonneg_right hthinpower (mul_nonneg hK.le hc.le)
    have hq' := mul_le_mul_of_nonneg_left hthin (by positivity : 0≤128*K)
    nlinarith only [hp,hq']
  have hendpoint : 4608*(100*(K*c)+2*c) ≤ d^(2*h) := by
    calc
      _ = (4608*(100*K+2))*c := by ring
      _ ≤ (4608*(100*K+2))*d^u := mul_le_mul_of_nonneg_left hcu (by positivity)
      _ ≤ d^(u/2) := HE d hd hdE'
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hmass : O (d^a₁) ≤ O (q/4)*O (d^h) := by
    have hp := (HM d hd hdM').trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hh₁₂)
    have hp' : 4*d^a₁ ≤ d^h*q := (div_le_iff₀ hq).mp
      (by simpa only [div_mul_eq_mul_div] using hp)
    rw [O,← ENNReal.ofReal_mul (by positivity : 0≤q/4)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith only [hp'])
  have hbroad : d^(-a₁) ≤ (q/2)*d^(-a₂) := by
    have hp := HB d hd hdB'
    have hp' : 2*d^(-a₁) ≤ d^(-a₂)*q := (div_le_iff₀ hq).mp
      (by simpa only [div_mul_eq_mul_div] using hp)
    nlinarith only [hp']
  obtain ⟨D₁,y,w,ha₁,hw,HD₁,Hcaps₁,hclass⟩ := Hcell D hd hd1 hdθ
    (by dsimp [a₁]; linarith) (by dsimp [a₁,a₂]; linarith)
    (by positivity : 0≤100*(K*c)) hendpoint hmass hbroad hA HD Hcaps
  have hdensity : O (d^r)*O (128*K^3*θ/ρ) ≤ O (d^a₂) := by
    have hp := HV d hd hdV'
    rw [Real.rpow_add hd] at hp
    have hp' := hp.trans (mul_le_mul_of_nonneg_left hρlo (Real.rpow_nonneg hd.le a₂))
    rw [O,← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le r)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ((128*K^3*θ)*d^r)/ρ := by ring
      _ ≤ _ := (div_le_iff₀ hρ).mpr hp'
  have hangular : d^(-a₂)*(1/ρ)^(ω*ζ/100) ≤ d^(-r) := by
    have hrbase : 1 ≤ 1/ρ := (le_div_iff₀ hρ).mpr (by simpa using hρ1)
    have hrpow : (1/ρ)^(ω*ζ/100) ≤ 1/ρ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrbase hβ1
    have hrinv : 1/ρ ≤ d^(-t) := by
      rw [Real.rpow_neg hd.le]
      simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hd t) hρlo
    calc
      _ ≤ d^(-a₂)*d^(-t) := mul_le_mul_of_nonneg_left (hrpow.trans hrinv) (by positivity)
      _ = d^(-a₂ + -t) := (Real.rpow_add hd _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by dsimp [a₂,t]; linarith)
  obtain ⟨D₂,ha₂,_,HD₂,Hcaps₂,hclear⟩ := capped_axial_reframe D₁ hd hd1
    (by dsimp [a₂]; positivity) (by dsimp [a₂]; linarith) hθ (by norm_num [θ])
    (by norm_num [θ,K]) hdc (by simpa only [ha₁] using hthinold)
    (hsmall.trans (by norm_num [θ])) hβ hdensity hangular
    (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.2) hw HD₁ Hcaps₁ hclass
  have hAd := admissible_mono hd hd1 hhr hA
  have hδKc : 4*d ≤ K*c := hdc.trans (by dsimp [K]; linarith)
  have hthin₂ : D₂.a ≤ d^(e/100)*(θ*(K*c)) := by simpa only [ha₂,ha₁] using hthinnew
  rcases HT hd hdT' hr.le le_rfl hAd θ (K*c) D₂ HD₂ Hcaps₂
    (by norm_num [θ]) hsmall hδKc hthin₂ hclear with hg | hs
  · exact Or.inl hg
  · have hunit : (16384:ℝ)*θ = 1 := by norm_num [θ]
    have hlen : (32:ℝ)*(K*c) = 8388608*c := by norm_num [K]; ring
    rw [hunit,hlen] at hs
    exact Or.inr (HJ hd hdJ' heJ (admissible_mono hd hd1 (hhr.trans hre) hA) hs
      (Real.rpow_le_one hd.le hd1 (by linarith)))

end WangZahlLot.Obl.wz_broad_grains_improvement
