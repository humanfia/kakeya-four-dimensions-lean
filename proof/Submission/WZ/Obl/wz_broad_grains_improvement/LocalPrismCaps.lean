-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.LocalPrismCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.UnionMultiplicityCut
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismPiece

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (PrismPiece)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (bodyCount body_mass_le_of_count)
open WangZahlLot.Obl.wz_broad_grains_initialization (body_count_cut)

/-- A single dense broad prism admits a capped dense broad subpiece. The
selection keeps a logarithmic share of union volume; global incidence
retention is supplied later by residual greedy extraction. -/
theorem capped_cut_of_good_prism {n N J : ℕ} {ω ζ d h h' a c s : ℝ}
    {ρ : Fin J → ℝ} {x v : Fin n → V} {y w : Fin N → V}
    (Q : PrismPiece n N J) (hd : 0 < d) (hd1 : d ≤ 1) (hhh : h ≤ h')
    (H : Q.Good ω ζ d h a c s ρ x v y w)
    (hbudget : 2*(Nat.log 2 n+1:ℕ)*d^h' ≤ d^h) :
    ∃ C : Set V, MeasurableSet C ∧
      (cutPrismPiece Q C).Good ω ζ d h' a c s ρ x v y w ∧
      PrismPieceCap d h' a c ρ (cutPrismPiece Q C) := by
  classical
  obtain ⟨ha,hab,hbc,hc,hW,hdense,hcross,hbroad⟩ := H
  obtain ⟨C,hcap,hCm,hsub,hm,hvolume,hlevel⟩ :=
    common_multiplicity_union_cut Q.piece (fun i => (hW i).1)
  let R := cutPrismPiece Q C
  have hRm (i : Fin n) : MeasurableSet (R.piece i) := (hW i).1.inter hCm
  have hunion : (⋃ i,R.piece i)=C := by
    apply subset_antisymm
    · exact iUnion_subset fun _ => inter_subset_right
    · intro p hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hsub hp)
      exact mem_iUnion.mpr ⟨i,hi,hp⟩
  have hlow (p : V) : hcap*bodyCount (fun _ : Fin 1 => C) p ≤ bodyCount R.piece p := by
    change _ ≤ bodyCount (fun i => Q.piece i ∩ C) p
    rw [body_count_cut]
    by_cases hp : p ∈ C
    · simpa [bodyCount,hp] using (hlevel p hp).1
    · simp [bodyCount,hp]
  have hmass : O hcap*volume C ≤ ∑ i,volume (R.piece i) := by
    simpa only [Fin.sum_univ_one] using body_mass_le_of_count (fun _ : Fin 1 => hCm) hRm hm.le hlow
  have hupper (p : V) : bodyCount R.piece p ≤ 2*hcap := by
    change bodyCount (fun i => Q.piece i ∩ C) p ≤ _
    rw [body_count_cut]
    by_cases hp : p ∈ C
    · simpa only [hp,ite_true] using (hlevel p hp).2
    · simp only [hp,ite_false]
      positivity
  let U := P a (ρ Q.scale*c) c Q.center Q.frame
  let K := Nat.log 2 n+1
  have hK : (K:ENNReal) ≠ 0 := by simp [K]
  have hKt : (K:ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hbudgetE : (K:ENNReal)*(2*O (d^h')) ≤ O (d^h) := by
    calc
      _ = O (2*(K:ℝ)*d^h') := by
        rw [O,ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2*K),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  have hdense2 : (2*O (d^h'))*volume U ≤ volume C := by
    apply (ENNReal.mul_le_mul_iff_right hK hKt).mp
    calc
      _ = ((K:ENNReal)*(2*O (d^h')))*volume U := (mul_assoc _ _ _).symm
      _ ≤ O (d^h)*volume U := mul_le_mul' hbudgetE le_rfl
      _ ≤ volume (⋃ i,Q.piece i) := hdense
      _ ≤ _ := hvolume
  have hdense' : O (d^h')*volume U ≤ volume C := by
    exact (mul_le_mul' (le_mul_of_one_le_left' (by norm_num : (1:ENNReal)≤2)) le_rfl).trans hdense2
  refine ⟨C,hCm,?_,?_⟩
  · refine ⟨ha,hab,hbc,hc,fun i => ⟨hRm i,inter_subset_left.trans (hW i).2⟩,?_,
      fun i hi => hcross i (hi.mono inter_subset_left),?_⟩
    · change O (d^h')*volume U ≤ volume (⋃ i,R.piece i)
      rw [hunion]
      exact hdense'
    · intro p u r hu hdr hrρ
      change q n {i | p ∈ Q.piece i ∩ C ∧ _} ≤ _*q n {i | p ∈ Q.piece i ∩ C}
      by_cases hp : p ∈ C
      · have he := hbroad p u r hu hdr hrρ
        simp only [mem_inter_iff,hp,and_true] at ⊢
        exact he.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hhh))
            (Real.rpow_nonneg (div_nonneg (hd.le.trans hdr) (hd.le.trans (hdr.trans hrρ))) _))
          (Nat.cast_nonneg _))
      · simp only [cutPrismPiece,mem_inter_iff,hp,and_false,false_and,
          Set.setOf_false,q,Set.ncard_empty,Nat.cast_zero,mul_zero,le_refl]
  · refine ⟨2*hcap,by positivity,hupper,?_⟩
    change O (d^h'*(2*hcap))*volume U ≤ _
    calc
      _ = O hcap*((2*O (d^h'))*volume U) := by
        rw [O,ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat]
        ring
      _ ≤ O hcap*volume C := mul_le_mul' le_rfl hdense2
      _ ≤ _ := hmass

end WangZahlLot.Obl.wz_broad_grains_improvement
