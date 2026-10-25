-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedMoveTwo.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedCappedLengthening
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedGainTransfer
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.ThickGrains
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.SharpMultiplicity

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- Move 2 with its full original-indexed output for scalar-aligned fine axes.
The two counting cases use the accepted thick-grain and fibre estimates; the
remaining case uses capped local lengthening and exact carriers. -/
theorem aligned_move_two {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      ∀ ρ c, J ω ζ d η ρ c n x v Y 1 →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        J ω ζ d ε ρ c n x v Y 2 ∨
        ∃ ρ' c', J ω ζ d ε ρ' c' n x v Y 0 ∧ d^(-ζ/2)*c ≤ c' := by
  obtain ⟨b,αL,κL,ηL,dL,hb,hb1,hαL,hκL,hηL,hηLε,hdL,hdL100,HL⟩ :=
    aligned_capped_lengthening_state hσ hσ2 hω hω1 hE hζ hζω hε
  obtain ⟨κT,ηT,dT,hκT,hηT,hdT,_,HT⟩ :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.thick_grains_gain hσ.le hσ2 hω hE hb hb1
  obtain ⟨κM,ηM,dM,hκM,hηM,hdM,HM⟩ :=
    WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.quadratic_low_multiplicity_gain
      hσ.le (by linarith : σ ≤ 1) hω
  let α := min αL (min (b*ω/2) (ω/100))
  let κ := min κL (min κT κM)
  let η := min ηL (min ηT ηM)
  have hα : 0 < α := by dsimp [α]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hηL' : η ≤ ηL := min_le_left _ _
  have hηT' : η ≤ ηT := (min_le_right _ _).trans (min_le_left _ _)
  have hηM' : η ≤ ηM := (min_le_right _ _).trans (min_le_right _ _)
  have hαL' : α ≤ αL := min_le_left _ _
  have hαT' : α ≤ b*ω/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hαM' : α ≤ ω/100 := (min_le_right _ _).trans (min_le_right _ _)
  have hκL' : κ ≤ κL := min_le_left _ _
  have hκT' : κ ≤ κT := (min_le_right _ _).trans (min_le_left _ _)
  have hκM' : κ ≤ κM := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨α,κ,η,min dL (min dT dM),hα,hκ,hη,hηL'.trans hηLε,
    by positivity,(min_le_left _ _).trans hdL100,?_⟩
  intro d hd hdd n x v Y hA haxes ρ c hJ
  have hdL' := hdd.trans (min_le_left _ _)
  have hdT' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdM' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hdL'.trans hdL100).trans (by norm_num)
  by_cases hρ : ρ ≤ d^(ω/100)
  · obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ :=
      stage_mono hd hd1 (hηL'.trans hηLε) hJ
    exact Or.inr (Or.inl ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,
      fun _ => hstop.1 (by decide),fun _ => hρ,by omega⟩)
  have hρlarge : d^(ω/100) < ρ := lt_of_not_ge hρ
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ := hJ
  by_cases hthick : 2*d^(1-b) ≤ a
  · exact Or.inl ((gain_mono hd hd1 hαT' hκT' hκ.le).trans
      (HT d η hd hdT' hη.le hηT' n x v Y hA S Z ρ N y w f True hC a c 0 g hH hthick))
  have hthin := lt_of_not_ge hthick
  obtain ⟨L,z,e,B,γ,m,hda,hab,hbc,hc1,hgeom,hdisj,hunion,hmass,hmult,hrest⟩ := hH
  have hH : H d η n x v S Z ρ N y w f a c 0 g :=
    ⟨L,z,e,B,γ,m,hda,hab,hbc,hc1,hgeom,hdisj,hunion,hmass,hmult,hrest⟩
  have hc : 0 < c := hd.trans_le (hda.trans (hab.trans hbc))
  by_cases hlow : m ≤ d^(-(24*ω/25))
  · have hρ1 : ρ ≤ 1 := by nlinarith only [hc,hbc]
    have hcount : ∀ k p, q n {i | i ∈ S ∧ f i=k ∧ p ∈ Z i} ≤ 2*d^(-(24*ω/25)) := by
      intro k p
      by_cases hp : ∃ i ∈ S, f i=k ∧ p ∈ Z i
      · exact (hmult k p hp).2.trans (by linarith)
      · have hempty : {i | i ∈ S ∧ f i=k ∧ p ∈ Z i} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact hp ⟨i,hi⟩
        rw [hempty]
        simp only [q,Set.ncard_empty,Nat.cast_zero]
        positivity
    exact Or.inl ((gain_mono hd hd1 hαM' hκM' hκ.le).trans
      (HM d η hd hdM' hη hηM' n x v Y hA S Z ρ N y w f hC hρlarge.le hρ1 hcount))
  have hhigh : ∀ k p, (∃ i ∈ S, f i=k ∧ p ∈ Z i) →
      d^(-(24*ω/25)) < q n {i | i ∈ S ∧ f i=k ∧ p ∈ Z i} :=
    fun k p hp => (lt_of_not_ge hlow).trans_le (hmult k p hp).1
  obtain ⟨u,t,hcap,hmid,halign⟩ := haxes
  rcases HL hd hdL' hηL' hA hcap hmid halign S Z ρ N y w f a c g
      hC hBr hH hρlarge hthin hhigh with hgain | hs
  · exact Or.inl ((gain_mono hd hd1 hαL' hκL' hκ.le).trans hgain)
  · obtain ⟨ρ',c',hlength,hJ'⟩ := hs
    refine Or.inr (Or.inr ⟨ρ',c',hJ',le_trans ?_ hlength⟩)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) hc.le

end WangZahlLot.Obl.wz_broad_grains_improvement
