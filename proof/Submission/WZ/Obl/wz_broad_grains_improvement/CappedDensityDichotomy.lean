-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedDensityDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedNarrowStage
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismNarrowCaps
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedCut
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.DensitySplit

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData prism_incidence_density_split select_capped_cut)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (bodyCount confinementDensity geometricPacketOverlap rotated_boxAxis)

/-- The density dichotomy can return capped stage-two data directly. Thus its
overlap branch does not require a new multiplicity normalization afterwards. -/
theorem density_or_capped_stage_two
    {ω ζ d h h₁ h₂ h₃ h₄ h₅ ρ c τ s R lam : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : 0 ≤ h) (hh₁ : h ≤ h₁)
    (hh₂ : h₁ ≤ h₂) (hh₃ : h₂ ≤ h₃) (hh₄ : h₃ ≤ h₄) (hh₅ : h₄ ≤ h₅)
    (hβ : 0 ≤ ω*ζ/100) (hρsmall : ρ ≤ 1/16384) (hcsmall : c ≤ 1/1048576)
    (hdc : 4*d ≤ c) (hτ : 0 < τ) (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ*s*c)
    (hR : 0 < R) (hRs : R ≤ (s/2)*ρ*c) (hlam : 0 ≤ lam)
    (hcutmass : O (d^h₁) ≤ (1/4:ENNReal)*O (d^h))
    (hcutdense : O (d^h₁) ≤ O (τ/4))
    (hnarrowmass : O (d^h₂) ≤ (1/4:ENNReal)*O (d^h₁))
    (hnarrowdense : O (d^h₂) ≤ O (τ/4/4))
    (hselect : (((10^40+1:ℕ):ENNReal)^14)*O (d^h₃) ≤ O (d^h₂))
    (hmerge : 8796093022208*d^h₄*ρ*s*c ≤ d^h₃*D.a)
    (hangular : d^(-h₃)*(16384:ℝ)^(ω*ζ/100) ≤ d^(-h₄))
    (hfair : O (d^h₅) ≤ (geometricPacketOverlap:ENNReal)⁻¹*O (d^h₄))
    (htransverse : 46080*lam < confinementDensity D.a ρ c (τ/4) s)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYI : ∀ i, Y i ⊆ I) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hYpos : 0 < ∑ i,volume (Y i)) (H : D.Valid ω ζ d h ρ c x v Y 1)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 < m j)
    (hcount : ∀ j p, bodyCount (fun i => D.W i j) p ≤ m j)
    (haverage : ∀ j, O (τ*m j)*volume (P D.a (ρ*c) c (D.z j) (D.e j)) ≤
      ∑ i,volume (D.W i j))
    (hclear : ∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ*c) c (D.z j) (D.e j),
      96*c < dist p (x i) ∧ 96*c < dist p (x i+v i)) :
    (∃ Z : Fin n → Set V, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1/2:ENNReal)*(∑ i,∑ j,volume (D.W i j)) ≤ ∑ i,volume (Z i) ∧
      ∀ i p, p ∈ Z i → O (lam*R^3) ≤ volume ((⋃ i,Y i) ∩ ball p R)) ∨
    ∃ D' : PrismData n, D'.Valid ω ζ d h₅ (16384*ρ) (32*c) x v Y 2 ∧
      D'.HasCaps d h₅ (16384*ρ) (32*c) := by
  rcases prism_incidence_density_split D hR hYm hYI H with hdense | hsparse
  · exact Or.inl hdense
  obtain ⟨B,hBm,hBU,hupper,hretain⟩ := hsparse
  obtain ⟨L,f,hf,Hc,hcountc,haveragec⟩ := select_capped_cut D hd hd1 hh₁ hτ
    hcutmass hcutdense H hYI m hm hcount haverage B hBm hretain
  let Dc := (D.select D.s f id (D.γ ∘ f)).cut (fun _ => B)
  have hasc : Dc.a ≤ s*ρ*c := by change D.a ≤ _; nlinarith [has]
  rcases capped_weighted_fibre_narrow Dc hd hd1 hh₂ hnarrowmass hnarrowdense
      (by positivity : 0 < τ/4) Hc hYI hs hs1 hasc hR hRs hlam
      (m ∘ f) (fun j => hm (f j)) hcountc haveragec B (fun _ _ => inter_subset_right)
      hBU hupper with hden | hn
  · exact (not_le_of_gt htransverse hden).elim
  obtain ⟨rot,hrot,C,Hn,Hcapn,hC,hnarrow⟩ := hn
  have hc : 0 < c := hd.trans_le (H.1.trans (H.2.1.trans H.2.2.1))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hd.trans_le (H.1.trans H.2.1))).resolve_right
    (by rintro ⟨_,hn⟩; linarith) |>.1
  apply Or.inr
  apply capped_narrow_stage_two (Dc.cut C) hd hd1 (hh.trans (hh₁.trans hh₂)) hh₃ hh₄ hh₅
    hβ hρsmall hcsmall hdc hs hs1 has hselect hmerge hangular hfair hv hYI hYT hYpos Hn Hcapn rot
  · intro k
    change Fin Dc.N at k
    change |rot k (Dc.w k) 0| ≤ ρ ∧ |rot k (Dc.w k) 1| ≤ ρ
    rw [hrot]
    simpa using And.intro hρ.le hρ.le
  · intro i j hi p hp
    exact hclear i (f j) (hi.mono (inter_subset_left.trans inter_subset_left)) p hp
  · dsimp only [PrismData.cut]
    intro j j' p he hp hp'
    apply Or.inr
    have hpC : p ∈ C j := by rwa [← (hC j).2.2]
    have hpC' : p ∈ C j' := by rwa [← (hC j').2.2]
    simpa only [rotated_boxAxis] using hnarrow j j' p he hpC hpC'

end WangZahlLot.Obl.wz_broad_grains_improvement
