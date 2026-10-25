-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedAllScaleState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedSmallState
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedMacroState
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.UnitInitialization
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WholePrism
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.ShortLength

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData initialization_at_one gain_of_nonthin_prisms short_length_at_separated_scale
   G_iff_data G_scales)
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine (exists_power_absorption)

/-- Capped exact prism data at any permitted coarse radius gives a gain or
a full original-indexed grain state. The coarse radius never decreases and
the length loss can be prescribed arbitrarily. -/
theorem capped_prisms_gain_or_state_with_length {σ ω ζ ε ell : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) (hell : 0 < ell) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      d^(1-ω/100) ≤ ρ →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ ρ' c', ρ ≤ ρ' ∧ d^ell*c ≤ c' ∧
          (d^(1-ell) < c → c ≤ c') ∧ J ω ζ d ε ρ' c' n x v Y 0 := by
  let β := ω*ζ/100
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := by
    have hζ1 : ζ ≤ 1 := by linarith
    dsimp [β]
    nlinarith only [hω1,hζ1,hω,hζ]
  let u := (ω/100)*β/8
  have hu : 0 < u := by dsimp [u]; positivity
  let b := min ell 1 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    have hh : min ell 1 ≤ 1 := min_le_right _ _
    dsimp [b]; linarith
  have hbell : b ≤ ell := by
    have hh : min ell 1 ≤ ell := min_le_left _ _
    dsimp [b]; linarith
  obtain ⟨αI,κI,ηI,dI,hαI,hκI,hηI,hηIε,hdI,hdI100,HI⟩ :=
    initialization_at_one hσ hσ2 hω hω1 hE hζ hζω hε
  obtain ⟨κN,ηN,τN,dN,hκN,hηN,hτN,_,hdN,_,HN⟩ :=
    gain_of_nonthin_prisms hσ.le hσ2 hω hω1 hE hb hb1
  obtain ⟨αM,κM,ηM,tM,dM,hαM,hκM,hηM,_,htM,hdM,_,HM⟩ :=
    macroscopic_capped_prisms_gain_or_state hσ.le hσ2 hω hω1 hE hε
      (half_pos hτN) hu hβ.le hβ1
  let t := min tM (min (τN/4) u)
  have ht : 0 < t := by dsimp [t]; positivity
  have httM : t ≤ tM := min_le_left _ _
  have htτ : t ≤ τN/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htu : t ≤ u := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨αS,κS,ηS,dS,hαS,hκS,hηS,_,hdS,_,HS⟩ :=
    small_capped_prisms_gain_or_state hσ.le hσ2 hω hω1 hE hε ht hβ.le hβ1
  obtain ⟨dL,hdL,_,HL⟩ := short_length_at_separated_scale
    (τ := ω/100) (by positivity) (by linarith) hβ hβ1
  obtain ⟨d4,hd4,H4⟩ := exists_power_absorption (C := 4) (p := 1) (r := 1-ell)
    (by norm_num) (by linarith)
  obtain ⟨d8,hd8,H8⟩ := exists_power_absorption (C := 8) (p := u) (r := 0)
    (by norm_num) hu
  let αN := b*ω/2
  let α := min αI (min αN (min αM αS))
  let κ := min κI (min κN (min κM κS))
  let η := min ηI (min ηN (min ηM (min ηS ((ω/100)*β/12))))
  have hα : 0 < α := by dsimp [α,αN]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηI' : η ≤ ηI := min_le_left _ _
  have hηN' : η ≤ ηN := (min_le_right _ _).trans (min_le_left _ _)
  have hηM' : η ≤ ηM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηS' : η ≤ ηS := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hηL : η ≤ (ω/100)*β/12 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hαI' : α ≤ αI := min_le_left _ _
  have hαN' : α ≤ b*ω/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hαM' : α ≤ αM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hαS' : α ≤ αS := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hκI' : κ ≤ κI := min_le_left _ _
  have hκN' : κ ≤ κN := (min_le_right _ _).trans (min_le_left _ _)
  have hκM' : κ ≤ κM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκS' : κ ≤ κS := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨α,κ,η,min dI (min dN (min dM (min dS (min dL (min d4 d8))))),
    hα,hκ,hη,hηI'.trans hηIε,by positivity,(min_le_left _ _).trans hdI100,?_⟩
  intro d h n x v Y hd hdd hh hA ρ c D HD Hcaps hbase
  have hcuts : d≤dI ∧ d≤dN ∧ d≤dM ∧ d≤dS ∧ d≤dL ∧ d≤d4 ∧ d≤d8 := by
    simpa only [le_min_iff] using hdd
  obtain ⟨hdI',hdN',hdM',hdS',hdL',hd4',hd8'⟩ := hcuts
  have hd1 : d ≤ 1 := (hdI'.trans hdI100).trans (by norm_num)
  obtain ⟨_,hρ,hρ1,_,hc,_⟩ := G_scales hd (G_iff_data.mpr ⟨D,HD⟩)
  by_cases hshort : c ≤ d^(1-ell)
  · rcases HI d hd hdI' n x v Y (admissible_mono hd hd1 (hh.trans hηI') hA) with hg | hs
    · exact Or.inl ((gain_mono hd hd1 hαI' hκI' hκ.le).trans hg)
    · obtain ⟨c',hs⟩ := hs
      have hlength : d ≤ c' := by
        obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase',hg,hbr,hG,_⟩ := hs
        obtain ⟨L,z,e,B,γ,m,ha,hab,hbc,_⟩ := hG
        exact ha.trans (hab.trans hbc)
      have hp : d^ell*c ≤ d := by
        calc
          _ ≤ d^ell*d^(1-ell) := mul_le_mul_of_nonneg_left hshort (by positivity)
          _ = d := by rw [← Real.rpow_add hd]; ring_nf; rw [Real.rpow_one]
      exact Or.inr ⟨1,c',hρ1,hp.trans hlength,
        fun hlong => False.elim (not_lt_of_ge hshort hlong),loose_to_stage_zero hs⟩
  have hdc : 4*d ≤ c := by
    have hp := H4 d hd hd4'
    rw [Real.rpow_one] at hp
    exact hp.trans (le_of_not_ge hshort)
  have hcu : c ≤ d^u := (HL d h hd hdL' (hh.trans hηL) n x v Y hA ρ c D 1 HD hbase).le
  have hlength : d^ell*c ≤ c := mul_le_of_le_one_left hc.le (Real.rpow_le_one hd.le hd1 hell.le)
  by_cases hsmall : ρ ≤ d^t
  · have hct : c ≤ d^t := hcu.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 htu)
    rcases HS hd hdS' (hh.trans hηS') hA ρ c D HD Hcaps hbase hsmall hct hdc with hg | hs
    · exact Or.inl ((gain_mono hd hd1 hαS' hκS' hκ.le).trans hg)
    · exact Or.inr ⟨16384*ρ,32*c,by linarith,by linarith,fun _ => by linarith,hs⟩
  have hρt : d^t ≤ ρ := le_of_not_ge hsmall
  by_cases hthin : D.a ≤ d^(τN/2)*c
  · have hρM : d^tM ≤ ρ := (Real.rpow_le_rpow_of_exponent_ge hd hd1 httM).trans hρt
    rcases HM hd hdM' (hh.trans hηM') hA ρ c D HD Hcaps hρM hcu hdc hthin with hg | hs
    · exact Or.inl ((gain_mono hd hd1 hαM' hκM' hκ.le).trans hg)
    · exact Or.inr ⟨1,8388608*c,hρ1,by linarith,fun _ => by linarith,hs⟩
  have hc8 : c ≤ 1/8 := by
    have hp := H8 d hd hd8'
    rw [Real.rpow_zero] at hp
    linarith
  have hclow : d^(1-b) ≤ 8*c := by
    have hp := (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : 1-ell ≤ 1-b)).trans
      (le_of_not_ge hshort)
    linarith
  have hround : d^τN ≤ D.a*ρ/c := by
    calc
      _ ≤ d^(τN/2+t) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      _ = d^(τN/2)*d^t := Real.rpow_add hd _ _
      _ ≤ d^(τN/2)*ρ := mul_le_mul_of_nonneg_left hρt (by positivity)
      _ = (d^(τN/2)*c)*ρ/c := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_of_not_ge hthin) hρ.le) hc.le
  exact Or.inl ((gain_mono hd hd1 hαN' hκN' hκ.le).trans
    (HN d h hd hdN' (hh.trans hηN') n x v Y hA ω ζ ρ c D HD hclow hc8 hround))

/-- The original all-scale interface, with an arbitrarily small prescribed
power loss in grain length. -/
theorem capped_prisms_gain_or_state {σ ω ζ ε ell : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) (hell : 0 < ell) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      d^(1-ω/100) ≤ ρ →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ ρ' c', ρ ≤ ρ' ∧ d^ell*c ≤ c' ∧ J ω ζ d ε ρ' c' n x v Y 0 := by
  obtain ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,H⟩ :=
    capped_prisms_gain_or_state_with_length hσ hσ2 hω hω1 hE hζ hζω hε hell
  refine ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,?_⟩
  intro d h n x v Y hd hdd hh hA ρ c D HD Hcaps hbase
  rcases H hd hdd hh hA ρ c D HD Hcaps hbase with hg | hs
  · exact Or.inl hg
  · obtain ⟨ρ',c',hρ,hc,_,hs⟩ := hs
    exact Or.inr ⟨ρ',c',hρ,hc,hs⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
