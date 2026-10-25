-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.RoundedLocalPrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.TransverseWidthPalette
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.AngularScale
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (PrismPiece Crosses G)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale (dyExp)

/-- The broadness radius corresponding to a rounded transverse width. -/
def transverseRadiusPalette (δ c : ℝ)
    (k : Fin ((dyExp 1 δ+1)*(dyExp 1 δ+1))) : ℝ :=
  (transverseWidthPalette δ c k).2/c

/-- A dense broad prism supplies a local piece in the fixed transverse
palette. Whole-tube containment uses a common auxiliary unit carrier. -/
theorem good_piece_in_width_palette
    {ω ζ δ h h' a ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {R W : Fin n → Set V} {z : V} {e : V ≃ₗᵢ[ℝ] V} (u : V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    (hβ : 0 ≤ ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hδa : δ ≤ a) (haρ : a ≤ ρ*c) (hρc : ρ*c ≤ c) (hc1 : c ≤ 1)
    (hTI : ∀ i,T δ (x i) (v i) ⊆ I)
    (hW : ∀ i,MeasurableSet (W i) ∧ W i ⊆ R i ∩ P a (ρ*c) c z e)
    (hdense : O (δ^h)*volume (P a (ρ*c) c z e) ≤ volume (⋃ i,W i))
    (hcross : ∀ i,(W i).Nonempty → Crosses δ a (ρ*c) c (x i) (v i) z e)
    (hBr : ∀ p u r,‖u‖=1 → δ≤r → r≤ρ →
      q n {i | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖≤r} ≤
        δ^(-h)*(r/ρ)^(ω*ζ/100)*q n {i | p ∈ W i})
    (hdensity : 4*δ^h' ≤ δ^h) (hbroad : 2*δ^(-h) ≤ δ^(-h')) :
    ∃ B : PrismPiece n 1 ((dyExp 1 δ+1)*(dyExp 1 δ+1)),
      B.Good ω ζ δ h' (transverseWidthPalette δ c B.scale).1 c 1
        (transverseRadiusPalette δ c) x v (fun _ => 0) (fun _ => u) ∧
      ρ ≤ transverseRadiusPalette δ c B.scale ∧ ∀ i,B.piece i ⊆ R i := by
  have ha : 0 < a := hδ.trans_le hδa
  have hρcpos : 0 < ρ*c := ha.trans_le haρ
  have hc : 0 < c := hρcpos.trans_le hρc
  have hρ : 0 < ρ := pos_of_mul_pos_left hρcpos hc.le
  obtain ⟨k,hkδ,hkab,hkbc,hka,hka2,hkb,hkb2⟩ :=
    transverse_width_palette_round hδ hc1 hδa haρ hρc
  let a' := (transverseWidthPalette δ c k).1
  let b' := (transverseWidthPalette δ c k).2
  let ρ' := transverseRadiusPalette δ c k
  have hρ'c : ρ'*c=b' := div_mul_cancel₀ _ hc.ne'
  have hρρ' : ρ ≤ ρ' := (le_div_iff₀ hc).mpr hkb
  have hρ'2 : ρ' ≤ 2*ρ := (div_le_iff₀ hc).mpr (by nlinarith only [hkb2])
  have hρ' : 0 < ρ' := hρ.trans_le hρρ'
  have hsub : P a (ρ*c) c z e ⊆ P a' b' c z e := by
    intro p hp
    exact ⟨hp.1.trans (by dsimp [a']; linarith),hp.2.1.trans (by dsimp [b']; linarith),hp.2.2⟩
  have hvolume : volume (P a' b' c z e) ≤ (4:ENNReal)*volume (P a (ρ*c) c z e) :=
    prism_transverse_volume_le_four ha.le hρcpos.le (hδ.le.trans hkδ)
      (hρcpos.le.trans hkb) hc.le hka2 hkb2 z e
  have hdense' : O (δ^h')*volume (P a' b' c z e) ≤ volume (⋃ i,W i) := by
    calc
      _ ≤ O (δ^h')*((4:ENNReal)*volume (P a (ρ*c) c z e)) := mul_le_mul' le_rfl hvolume
      _ = O (4*δ^h')*volume (P a (ρ*c) c z e) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat,mul_assoc]
        exact mul_left_comm _ _ _
      _ ≤ O (δ^h)*volume (P a (ρ*c) c z e) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hdensity) le_rfl
      _ ≤ _ := hdense
  have hangular : δ^(-h)*(ρ'/ρ)^(ω*ζ/100) ≤ δ^(-h') := by
    have hr2 : ρ'/ρ ≤ 2 := (div_le_iff₀ hρ).mpr hρ'2
    have hp : (ρ'/ρ)^(ω*ζ/100) ≤ 2 :=
      (Real.rpow_le_rpow (by positivity) hr2 hβ).trans (by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hβ1)
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans (by simpa only [mul_comm] using hbroad)
  let B : PrismPiece n 1 ((dyExp 1 δ+1)*(dyExp 1 δ+1)) := ⟨k,0,z,e,W⟩
  refine ⟨B,?_,hρρ',fun i => (hW i).2.trans inter_subset_left⟩
  change δ≤a' ∧ a'≤ρ'*c ∧ ρ'*c≤c ∧ c≤1 ∧
    (∀ i,MeasurableSet (W i) ∧ W i ⊆ P a' (ρ'*c) c z e) ∧
    O (δ^h')*volume (P a' (ρ'*c) c z e) ≤ volume (⋃ i,W i) ∧
    (∀ i,(W i).Nonempty → T δ (x i) (v i) ⊆ T 1 0 u ∧
      Crosses δ a' (ρ'*c) c (x i) (v i) z e) ∧ _
  refine ⟨hkδ,by simpa only [hρ'c] using hkab,by simpa only [hρ'c] using hkbc,hc1,
    ?_,by simpa only [hρ'c] using hdense',?_,?_⟩
  · intro i
    exact ⟨(hW i).1,by simpa only [hρ'c] using ((hW i).2.trans inter_subset_right).trans hsub⟩
  · intro i hi
    constructor
    · intro p hp
      exact Metric.mem_thickening_iff.mpr
        ⟨0,left_mem_segment ℝ 0 (0+u),hTI i hp⟩
    · simpa only [hρ'c] using crosses_transverse_mono hc hka hkb (hcross i hi)
  · intro p
    exact WangZahlLot.Obl.wz_move_two_capped_prism_overlap.angular_bound_enlarge
      v {i | p ∈ W i} hδ hρ hρρ' hβ
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hh))
      hangular (hBr p)

/-- The global stage-zero prism predicate supplies a rounded local selector.
Only positivity of its input mass is used to choose a column. -/
theorem good_piece_in_width_palette_of_prisms
    {ω ζ δ h h' ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {R : Fin n → Set V} (u : V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    (hβ : 0 ≤ ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hTI : ∀ i,T δ (x i) (v i) ⊆ I) (hRpos : 0 < ∑ i,volume (R i))
    (hdensity : 4*δ^h' ≤ δ^h) (hbroad : 2*δ^(-h) ≤ δ^(-h'))
    (hG : G ω ζ δ h ρ c n x v R 0) :
    ∃ B : PrismPiece n 1 ((dyExp 1 δ+1)*(dyExp 1 δ+1)),
      B.Good ω ζ δ h' (transverseWidthPalette δ c B.scale).1 c 1
        (transverseRadiusPalette δ c) x v (fun _ => 0) (fun _ => u) ∧
      ρ ≤ transverseRadiusPalette δ c B.scale ∧ ∀ i,B.piece i ⊆ R i := by
  obtain ⟨a,s,L,N,z,e,W,y,w,γ,hδa,haρ,hρc,hc1,hW,hmass,hdense,hcross,hBr,_⟩ := hG
  have hL : 0 < L := by
    by_contra hn
    have he : L=0 := by omega
    subst L
    simp only [Fin.sum_univ_zero,Finset.sum_const_zero] at hmass
    have hp : 0 < O (δ^h)*∑ i,volume (R i) :=
      ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h),hRpos⟩
    exact (not_lt_of_ge hmass) hp
  let j : Fin L := ⟨0,hL⟩
  exact good_piece_in_width_palette u hδ hδ1 hh hβ hβ1 hδa haρ hρc hc1 hTI
    (fun i => ⟨(hW i j).1,(hW i j).2.1⟩) (hdense j)
    (fun i hi => (hcross i j hi).2) (hBr j) hdensity hbroad

end WangZahlLot.Obl.wz_broad_grains_improvement
