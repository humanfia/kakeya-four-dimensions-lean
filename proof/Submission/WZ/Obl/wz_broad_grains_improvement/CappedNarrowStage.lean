-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedNarrowStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPacketMerge
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarsePowerSelect
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseRestriction

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData select_power_two_coarse valid_select_coarse)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (dualLinear rotatedFrame boxAxis geometricPacketOverlap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)

/-- Coarse selection, packet merging, and fair disjointification preserve
normalized incidence caps throughout the narrow-prism construction. -/
theorem capped_narrow_stage_two {ω ζ d h h₁ h₂ h₃ ρ c s : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : 0 ≤ h)
    (hh₁ : h ≤ h₁) (hh₂ : h₁ ≤ h₂) (hh₃ : h₂ ≤ h₃)
    (hβ : 0 ≤ ω*ζ/100) (hρsmall : ρ ≤ 1/16384) (hcsmall : c ≤ 1/1048576)
    (hdc : 4*d ≤ c) (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ*s*c)
    (hselect : (((10^40+1:ℕ):ENNReal)^14)*O (d^h₁) ≤ O (d^h))
    (hmerge : 8796093022208*d^h₂*ρ*s*c ≤ d^h₁*D.a)
    (hangular : d^(-h₁)*(16384:ℝ)^(ω*ζ/100) ≤ d^(-h₂))
    (hfair : O (d^h₃) ≤ (geometricPacketOverlap:ENNReal)⁻¹*O (d^h₂))
    (hv : ∀ i, ‖v i‖ = 1) (hYI : ∀ i, Y i ⊆ I) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hYpos : 0 < ∑ i, volume (Y i))
    (H : D.Valid ω ζ d h ρ c x v Y 1) (Hcaps : D.HasCaps d h ρ c)
    (R : Fin D.N → V ≃ₗᵢ[ℝ] V)
    (hR : ∀ k, |R k (D.w k) 0| ≤ ρ ∧ |R k (D.w k) 1| ≤ ρ)
    (hclear : ∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ*c) c (D.z j) (D.e j),
      96*c < dist p (x i) ∧ 96*c < dist p (x i+v i))
    (hnarrow : ∀ j j' p, D.γ j = D.γ j' → p ∈ ⋃ i, D.W i j → p ∈ ⋃ i, D.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j')) (D.e j')) 0))) ≤ s) :
    ∃ D' : PrismData n, D'.Valid ω ζ d h₃ (16384*ρ) (32*c) x v Y 2 ∧
      D'.HasCaps d h₃ (16384*ρ) (32*c) := by
  classical
  have ha : 0 < D.a := hd.trans_le H.1
  have hc : 0 < c := ha.trans_le (H.2.1.trans H.2.2.1)
  have hρ : 0 < ρ := (mul_pos_iff.mp (ha.trans_le H.2.1)).resolve_right
    (by rintro ⟨_,hn⟩; linarith) |>.1
  have hmass := H.2.2.2.2.2.1
  have hpos : 0 < ∑ i, ∑ j, volume (D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd h)).ne' hYpos.ne').trans_le hmass
  have hX : X ρ D.N D.y D.w := by
    have hx := H.2.2.2.2.2.2.2.2.2.1
    rwa [(H.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)).1] at hx
  obtain ⟨L,N,f,g,γ,hf,hg,hγ,hX',hkeep⟩ := select_power_two_coarse D 14 hρ
    (by norm_num; linarith) H.2.2.2.2.2.2.2.2.2.2.1 hX hpos
  let Ds := D.select D.s f g γ
  have hmass' : O (d^h₁)*∑ i,volume (Y i) ≤ ∑ i,∑ j,volume (D.W i (f j)) := by
    let C : ENNReal := (((10^40+1:ℕ):ENNReal)^14)
    have hC0 : C ≠ 0 := by simp [C]
    have hCtop : C ≠ ⊤ := by simp [C]
    apply (ENNReal.mul_le_mul_iff_left hC0 hCtop).mp
    calc
      (O (d^h₁)*∑ i,volume (Y i))*C = (C*O (d^h₁))*∑ i,volume (Y i) := by ring
      _ ≤ O (d^h)*∑ i,volume (Y i) := mul_le_mul' hselect le_rfl
      _ ≤ ∑ i,∑ j,volume (D.W i j) := hmass
      _ ≤ C*∑ i,∑ j,volume (D.W i (f j)) := hkeep
      _ = _ := mul_comm _ _
  have Hs : Ds.Valid ω ζ d h₁ ρ c x v Y 1 :=
    valid_select_coarse D hd hd1 hh₁ H f hf g hg γ hγ hmass'
  have Hcaps_s : Ds.HasCaps d h₁ ρ c := caps_of_prism_selection hd ha.le hc.le hρ.le hρ.le
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 hh₁) hρ.le)
    ⟨rfl,f,hf,rfl,rfl,fun _ => rfl⟩ Hcaps
  have hXs : X (16384*ρ) Ds.N Ds.y Ds.w := by
    change X (16384*ρ) N (D.y ∘ g) (D.w ∘ g)
    convert hX' using 1 <;> norm_num
  let Rs : Fin Ds.N → V ≃ₗᵢ[ℝ] V := R ∘ g
  have hRs (k : Fin Ds.N) : |Rs k (Ds.w k) 0| ≤ ρ ∧ |Rs k (Ds.w k) 1| ≤ ρ := hR (g k)
  have hclear_s : ∀ i j, (Ds.W i j).Nonempty → ∀ p ∈ P Ds.a (ρ*c) c (Ds.z j) (Ds.e j),
      96*c < dist p (x i) ∧ 96*c < dist p (x i+v i) := fun i j => hclear i (f j)
  have hnarrow_s : ∀ j j' p, Ds.γ j = Ds.γ j' → p ∈ ⋃ i, Ds.W i j → p ∈ ⋃ i, Ds.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (Rs (Ds.γ j)) (Ds.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (Rs (Ds.γ j')) (Ds.e j')) 0))) ≤ s := by
    intro j j' p he hp hp'
    have he' : D.γ (f j) = D.γ (f j') := by
      rw [← hγ j,← hγ j']
      exact congrArg g he
    have hn := hnarrow (f j) (f j') p he' hp hp'
    dsimp only [Ds,PrismData.select,Rs,Function.comp_apply]
    rw [hγ j,hγ j']
    exact hn
  obtain ⟨Dm,Hm,Hcapm,hcount⟩ := capped_narrow_prism_merge Ds hd hd1 hh₂ (hh.trans hh₁)
    hβ hρsmall hcsmall hdc hs hs1 has hmerge hangular hv hYI hYT Hs Hcaps_s hXs Rs hRs
    hclear_s hnarrow_s
  apply capped_stage_two_of_bounded_overlap Dm (by norm_num [geometricPacketOverlap])
    hd hd1 hh₃ hfair hYI Hm Hcapm
  intro p k
  exact_mod_cast hcount k p

end WangZahlLot.Obl.wz_broad_grains_improvement
