-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedSmallPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedThinUniform
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData endpoint_clear_capped_prisms)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (geometricPacketOverlap)
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine (exists_power_absorption)

/-- At polynomially small coarse radius and grain length, capped prism data
gives a gain or capped stage two. The input has no aspect-ratio or endpoint
clearance restriction. -/
theorem small_prisms_gain_or_capped_stage_two {σ ω ζ ε t : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hβ : 0 ≤ ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1) :
    ∃ κ η d₀ : ℝ, 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      ρ ≤ d^t → c ≤ d^t → 4*d ≤ c →
      O (κ*d^(ω-(ε/100)*ω/2)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
      ∃ D' : PrismData n, D'.Valid ω ζ d ε (16384*ρ) (32*c) x v Y 2 ∧
        D'.HasCaps d ε (16384*ρ) (32*c) := by
  obtain ⟨κ,ηT,dT,hκ,hηT,_,hdT,hdT100,HT⟩ :=
    thin_prisms_gain_or_capped_stage_two hσ hσ2 hω hω1 hE hε hε1 hβ
  let θ := min ηT (ε/8)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθε : θ ≤ ε/8 := min_le_right _ _
  have hθT : θ ≤ ηT := min_le_left _ _
  obtain ⟨dE,hdE,HE⟩ := exists_power_absorption (C := 479232) (p := t) (r := t/2)
    (by norm_num) (by linarith)
  obtain ⟨dS,hdS,HS⟩ := exists_power_absorption (C := 1048576) (p := t) (r := 0)
    (by norm_num) ht
  obtain ⟨dH,hdH,HH⟩ := exists_power_absorption (C := 2) (p := θ) (r := θ/2)
    (by norm_num) (by linarith)
  let C : ℝ := ((10^40+1:ℕ):ℝ)^14
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨dSel,hdSel,HSel⟩ := exists_power_absorption (C := C) (p := ε/4) (r := ε/8)
    hC (by linarith)
  obtain ⟨dM,hdM,HM⟩ := exists_power_absorption (C := 8796093022208) (p := ε/2)
    (r := ε/4+ε/100) (by norm_num) (by linarith)
  obtain ⟨dA,hdA,HA⟩ := exists_power_absorption (C := 16384) (p := -(ε/4)) (r := -(ε/2))
    (by norm_num) (by linarith)
  have hK : 0 < (geometricPacketOverlap:ℝ) := by norm_num [geometricPacketOverlap]
  obtain ⟨dF,hdF,HF⟩ := exists_power_absorption (C := (geometricPacketOverlap:ℝ))
    (p := ε) (r := ε/2) hK (by linarith)
  refine ⟨κ,min (θ/2) (t/4),min dT (min dE (min dS (min dH (min dSel (min dM (min dA dF)))))),
    hκ,by positivity,(min_le_left _ _).trans (by linarith),by positivity,
    (min_le_left _ _).trans hdT100,?_⟩
  intro d h n x v Y hd hdd hhη hAd ρ c D HD Hcaps hρt hct hdc
  have hcut : d≤dT ∧ d≤dE ∧ d≤dS ∧ d≤dH ∧ d≤dSel ∧ d≤dM ∧ d≤dA ∧ d≤dF := by
    simpa only [le_min_iff] using hdd
  obtain ⟨hdT',hdE',hdS',hdH',hdSel',hdM',hdA',hdF'⟩ := hcut
  have hd1 : d ≤ 1 := (hdT'.trans hdT100).trans (by norm_num)
  have hhθ : h ≤ θ/2 := hhη.trans (min_le_left _ _)
  have hht : h ≤ t/4 := hhη.trans (min_le_right _ _)
  have hhθ' : h ≤ θ := by linarith
  have hc : 0 < c := hd.trans_le (HD.1.trans (HD.2.1.trans HD.2.2.1))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hd.trans_le (HD.1.trans HD.2.1))).resolve_right
    (by rintro ⟨_,hn⟩; linarith) |>.1
  have hsmall : d^t ≤ 1/1048576 := by
    have hh' := HS d hd hdS'
    rw [Real.rpow_zero] at hh'
    linarith
  have hρsmall : ρ ≤ 1/16384 := hρt.trans (hsmall.trans (by norm_num))
  have hcsmall := hct.trans hsmall
  have hbudget : 4608*(96*c+2*c+6*ρ) ≤ d^(2*h) := by
    calc
      _ ≤ 479232*d^t := by linarith
      _ ≤ d^(t/2) := HE d hd hdE'
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have htrim : O (d^θ) ≤ (1/2:ENNReal)*O (d^h) := by
    have hp := (HH d hd hdH').trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hhθ)
    have hh' : d^θ ≤ (1/2:ℝ)*d^h := by linarith
    have he := ENNReal.ofReal_le_ofReal hh'
    simpa only [O,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using he
  obtain ⟨D',hae,H',Hcaps',hclear⟩ := endpoint_clear_capped_prisms D hd hd1 hhθ'
    (by positivity : 0≤96*c) hbudget htrim hAd HD Hcaps
  by_cases hthin : D.a ≤ d^(ε/100)*(ρ*c)
  · exact HT hd hdT' hθ.le hθT (admissible_mono hd hd1 hhθ' hAd) ρ c D' H' Hcaps'
      hρsmall hcsmall hdc (by simpa only [hae] using hthin) hclear
  have hround : d^(ε/100)*(ρ*c) ≤ D'.a := by rw [hae]; exact le_of_not_ge hthin
  have hsel : (((10^40+1:ℕ):ENNReal)^14)*O (d^(ε/4)) ≤ O (d^θ) := by
    have hh' := (HSel d hd hdSel').trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hθε)
    have he := ENNReal.ofReal_le_ofReal hh'
    simpa only [C,O,ENNReal.ofReal_mul hC.le,ENNReal.ofReal_pow
      (by positivity : 0≤((10^40+1:ℕ):ℝ)),ENNReal.ofReal_natCast] using he
  have hmerge : 8796093022208*d^(ε/2)*ρ*1*c ≤ d^(ε/4)*D'.a := by
    calc
      _ = (8796093022208*d^(ε/2))*(ρ*c) := by ring
      _ ≤ d^(ε/4+ε/100)*(ρ*c) := mul_le_mul_of_nonneg_right (HM d hd hdM') (by positivity)
      _ = d^(ε/4)*(d^(ε/100)*(ρ*c)) := by rw [Real.rpow_add hd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hround (by positivity)
  have hang : d^(-(ε/4))*(16384:ℝ)^(ω*ζ/100) ≤ d^(-(ε/2)) := by
    calc
      _ ≤ d^(-(ε/4))*(16384:ℝ)^(1:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1) (by positivity)
      _ = 16384*d^(-(ε/4)) := by rw [Real.rpow_one]; ring
      _ ≤ _ := HA d hd hdA'
  have hfair : O (d^ε) ≤ (geometricPacketOverlap:ENNReal)⁻¹*O (d^(ε/2)) := by
    calc
      _ ≤ O (d^(ε/2)/(geometricPacketOverlap:ℝ)) := ENNReal.ofReal_le_ofReal
        ((le_div_iff₀ hK).mpr (by simpa only [mul_comm] using HF d hd hdF'))
      _ = _ := by rw [O,ENNReal.ofReal_div_of_pos hK,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hAd.1
  have hYpos : 0 < ∑ i,volume (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0<d^h*n*d^2)).trans_le hAd.2.2.2.1
  choose R hR using fun k =>
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.exists_rotation_last
      (H'.2.2.2.2.2.2.2.2.2.2.1 k)
  apply Or.inr
  apply capped_narrow_stage_two D' hd hd1 hθ.le (by linarith) (by linarith) (by linarith)
    hβ hρsmall hcsmall hdc (s := 1) (by norm_num) le_rfl
    (by simpa only [mul_one] using H'.2.1) hsel hmerge hang hfair
    (fun i => (hAd.2.1 i).1) (fun i => (hAd.2.1 i).2.2.2.trans (hAd.2.1 i).2.1)
    (fun i => (hAd.2.1 i).2.2.2) hYpos H' Hcaps' R ?_ hclear ?_
  · intro k
    rw [hR k]
    simpa using And.intro hρ.le hρ.le
  · intro j j' p he hp hp'
    exact Or.inl rfl

end WangZahlLot.Obl.wz_broad_grains_improvement
