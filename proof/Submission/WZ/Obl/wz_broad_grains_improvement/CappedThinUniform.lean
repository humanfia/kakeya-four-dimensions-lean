-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedThinUniform.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedDensityDichotomy
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedBudgets
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.NeighborhoodGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinementPowers

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData exists_capped_power_budgets gain_of_dense_neighborhoods)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (confinementDensity confinement_density_power_lower geometricPacketOverlap)

/-- Uniform thin-prism improvement with normalized caps retained in the
disjoint alternative. Its analytic inputs are the accepted confinement and
dense-neighborhood estimates. -/
theorem thin_prisms_gain_or_capped_stage_two {σ ω ζ ε : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 ≤ ω*ζ/100) :
    ∃ κ η d₀ : ℝ, 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      ρ ≤ 1/16384 → c ≤ 1/1048576 → 4*d ≤ c → D.a ≤ d^(ε/100)*(ρ*c) →
      (∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ*c) c (D.z j) (D.e j),
        96*c < dist p (x i) ∧ 96*c < dist p (x i+v i)) →
      O (κ*d^(ω-(ε/100)*ω/2)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
      ∃ D' : PrismData n, D'.Valid ω ζ d ε (16384*ρ) (32*c) x v Y 2 ∧
        D'.HasCaps d ε (16384*ρ) (32*c) := by
  let b := ε/100
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨κ,ηN,ν,dN,hκ,hηN,hν,_,hνb,hdN,hdN100,HN⟩ :=
    gain_of_dense_neighborhoods hσ hσ2 hω hω1 hE hb (by dsimp [b]; linarith)
  have hνε : ν ≤ ε/1000 := by dsimp [b] at hνb; nlinarith
  obtain ⟨dP,hdP,HP⟩ := exists_capped_power_budgets (β := ω*ζ/100) hε hν hνε
  obtain ⟨dC,hdC,HC⟩ := confinement_density_power_lower hν
  refine ⟨κ,min ηN (ν/10),min dN (min dP dC),hκ,by positivity,
    (min_le_right _ _).trans (by linarith),by positivity,(min_le_left _ _).trans hdN100,?_⟩
  intro d h n x v Y hd hdd hh hhη hA ρ c D H Hcaps hρsmall hcsmall hdc hthin hclear
  have hdN' := hdd.trans (min_le_left _ _)
  have hdP' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdC' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdlt : d < 1 := (hdN'.trans hdN100).trans_lt (by norm_num)
  have hd1 := hdlt.le
  have hhν : h ≤ ν/10 := hhη.trans (min_le_right _ _)
  have HB := HP d h hd hd1 hdP' hhν
  have ha : 0 < D.a := hd.trans_le H.1
  have hc : 0 < c := ha.trans_le (H.2.1.trans H.2.2.1)
  have hρ : 0 < ρ := (mul_pos_iff.mp (ha.trans_le H.2.1)).resolve_right
    (by rintro ⟨_,hn⟩; linarith) |>.1
  have hρc : 0 < ρ*c := mul_pos hρ hc
  have hρc1 : ρ*c ≤ 1 := H.2.2.1.trans H.2.2.2.1
  let r := D.a*d^(-b)
  let s := r/(ρ*c)
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hprod : ρ*s*c = r := by dsimp [s]; field_simp
  have hrle : r ≤ ρ*c := by
    calc
      _ ≤ (d^b*(ρ*c))*d^(-b) := mul_le_mul_of_nonneg_right hthin (Real.rpow_nonneg hd.le _)
      _ = (ρ*c)*(d^b*d^(-b)) := by ring
      _ = _ := by rw [← Real.rpow_add hd,add_neg_cancel,Real.rpow_zero,mul_one]
  have hs1 : s ≤ 1 := (div_le_one hρc).mpr hrle
  have has : D.a ≤ ρ*s*c := by
    rw [hprod]
    exact le_mul_of_one_le_right ha.le
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr hb.le))
  have hds : d ≤ s := by
    have hh' := mul_le_mul_of_nonneg_left hρc1 hs.le
    nlinarith [H.1]
  have hrlo : d^(1-b) ≤ r := by
    rw [sub_eq_add_neg,Real.rpow_add hd,Real.rpow_one]
    exact mul_le_mul_of_nonneg_right H.1 (Real.rpow_nonneg hd.le _)
  have hr1 : r ≤ 1 := hrle.trans hρc1
  have hquarter (u v : ℝ) (huv : 4*u ≤ v) : O u ≤ (1/4:ENNReal)*O v := by
    calc
      _ ≤ O ((1/4:ℝ)*v) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
        rw [O,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/4)]
        norm_num [ENNReal.ofReal_div_of_pos]
  have hcut := hquarter (d^ν) (d^h) (by linarith [HB.cut,Real.rpow_pos_of_pos hd ν])
  have hnarrow := hquarter (d^(2*ν)) (d^ν) HB.narrow
  have hνD : d^ν ≤ d^h/4 := by linarith [HB.cut,Real.rpow_pos_of_pos hd ν]
  have hnd : O (d^(2*ν)) ≤ O (d^h/4/4) := by
    apply ENNReal.ofReal_le_ofReal
    have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show ν ≤ 2*ν by linarith)
    linarith [HB.cut]
  have hconf := HC d hd hd1 hdC' D.a ρ c (d^h/4) s H.1 H.2.1 hρc1 hνD hds
  have hselect : (((10^40+1:ℕ):ENNReal)^14)*O (d^(3*ν)) ≤ O (d^(2*ν)) := by
    have hp := ENNReal.ofReal_le_ofReal HB.select
    simpa only [O,ENNReal.ofReal_mul (by positivity : 0≤(((10^40+1:ℕ):ℝ)^14)),
      ENNReal.ofReal_pow (by positivity : 0≤((10^40+1:ℕ):ℝ)),ENNReal.ofReal_natCast] using hp
  have hmerge : 8796093022208*d^(ε/2)*ρ*s*c ≤ d^(3*ν)*D.a := by
    calc
      _ = (8796093022208*d^(ε/2))*(ρ*s*c) := by ring
      _ = (8796093022208*d^(ε/2-b))*D.a := by
        rw [hprod,sub_eq_add_neg,Real.rpow_add hd]
        dsimp [r]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right HB.merge ha.le
  have hK : 0 < (geometricPacketOverlap:ℝ) := by norm_num [geometricPacketOverlap]
  have hfair : O (d^ε) ≤ (geometricPacketOverlap:ENNReal)⁻¹*O (d^(ε/2)) := by
    calc
      _ ≤ O (d^(ε/2)/(geometricPacketOverlap:ℝ)) := ENNReal.ofReal_le_ofReal
        ((le_div_iff₀ hK).mpr (by simpa only [mul_comm] using HB.fair))
      _ = _ := by
        rw [O,ENNReal.ofReal_div_of_pos hK,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hA.1
  have hYpos : 0 < ∑ i,volume (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0<d^h*n*d^2)).trans_le hA.2.2.2.1
  obtain ⟨m,hm,hcount,haverage⟩ := Hcaps
  rcases density_or_capped_stage_two D hd hd1 hh (by linarith : h≤ν)
      (by linarith : ν≤2*ν) (by linarith : 2*ν≤3*ν)
      (by linarith : 3*ν≤ε/2) (by linarith : ε/2≤ε)
      hβ hρsmall hcsmall hdc (Real.rpow_pos_of_pos hd h) hs hs1 has (half_pos hr)
      (by nlinarith [hprod] : r/2≤(s/2)*ρ*c) (Real.rpow_nonneg hd.le (12*ν))
      hcut (ENNReal.ofReal_le_ofReal hνD) hnarrow hnd hselect hmerge HB.angular hfair
      (HB.transverse.trans_le hconf) (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.1)
      (fun i => (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1) (fun i => (hA.2.1 i).2.2.2)
      hYpos H m hm hcount haverage hclear with hden | hstage
  · obtain ⟨Z,hZ,hretain,hden⟩ := hden
    let B := 1-Real.logb d r
    have hpow : d^(1-B) = r := by
      rw [show 1-B=Real.logb d r by dsimp [B]; ring]
      exact Real.rpow_logb hd hdlt.ne hr
    have hbB : b ≤ B := by
      have hpow' : d^(1-b) ≤ d^(1-B) := by rwa [hpow]
      have hh' := (Real.rpow_le_rpow_left_iff_of_base_lt_one hd hdlt).mp hpow'
      linarith
    have hB1 : B ≤ 1 := by
      have hpow' : d^(1-B) ≤ d^(0:ℝ) := by rw [hpow,Real.rpow_zero]; exact hr1
      have hh' := (Real.rpow_le_rpow_left_iff_of_base_lt_one hd hdlt).mp hpow'
      linarith
    apply Or.inl
    apply HN d B hd hdN' hbB hB1 n x v Y Z
      (admissible_mono hd hd1 (hhη.trans (min_le_left _ _)) hA) hZ
    · calc
        _ ≤ ((1/2:ENNReal)*O (d^h))*∑ i,volume (Y i) :=
          mul_le_mul' (hcut.trans (mul_le_mul' (by norm_num) le_rfl)) le_rfl
        _ ≤ (1/2:ENNReal)*(∑ i,∑ j,volume (D.W i j)) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl H.2.2.2.2.2.1
        _ ≤ _ := hretain
    · intro i p hp
      rw [hpow]
      exact hden i p hp
  · exact Or.inr hstage

end WangZahlLot.Obl.wz_broad_grains_improvement
