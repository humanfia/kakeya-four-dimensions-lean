-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.NarrowStageTwo.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PacketMerge
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarsePowerSelect
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseRestriction
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.LowOverlap

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, NarrowStageTwo.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V O I P T X q coarseLinear dualLinear rotatedFrame boxAxis geometricPacketOverlap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)

/-- Narrowness, endpoint clearance, and explicit error budgets imply the
full stage-two conclusion. Coarse enlargement and exact disjointification
are part of the construction. -/
theorem stage_two_of_narrow_prisms {ω ζ δ h h₁ h₂ h₃ ρ c s : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    (hh₁ : h ≤ h₁) (hh₂ : h₁ ≤ h₂) (hh₃ : h₂ ≤ h₃)
    (hβ : 0 ≤ ω * ζ / 100) (hρsmall : ρ ≤ 1 / 16384)
    (hcsmall : c ≤ 1 / 1048576) (hδc : 4 * δ ≤ c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ * s * c)
    (hselect : (((10 ^ 40 + 1 : ℕ) : ENNReal) ^ 14) * O (δ ^ h₁) ≤ O (δ ^ h))
    (hbudget : 8796093022208 * δ ^ h₂ * ρ * s * c ≤ δ ^ h₁ * D.a)
    (hangular : δ ^ (-h₁) * (16384 : ℝ) ^ (ω * ζ / 100) ≤ δ ^ (-h₂))
    (hfair : O (δ ^ h₃) ≤ (geometricPacketOverlap : ENNReal)⁻¹ * O (δ ^ h₂))
    (hv : ∀ i, ‖v i‖ = 1) (hYI : ∀ i, Y i ⊆ I) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hYpos : 0 < ∑ i, volume (Y i)) (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (R : Fin D.N → V ≃ₗᵢ[ℝ] V)
    (hR : ∀ k, |R k (D.w k) 0| ≤ ρ ∧ |R k (D.w k) 1| ≤ ρ)
    (hclear : ∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ * c) c (D.z j) (D.e j),
      96 * c < dist p (x i) ∧ 96 * c < dist p (x i + v i))
    (hnarrow : ∀ j j' p, D.γ j = D.γ j' → p ∈ ⋃ i, D.W i j → p ∈ ⋃ i, D.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j')) (D.e j')) 0))) ≤ s) :
    G ω ζ δ h₃ (16384 * ρ) (32 * c) n x v Y 2 := by
  classical
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, _, hmass, _, _, _, hX, hw, hcover, _⟩
  have hc : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hpos : 0 < ∑ i, ∑ j, volume (D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne' hYpos.ne').trans_le hmass
  rw [(hcover (by norm_num)).1] at hX
  obtain ⟨L, N, f, g, γ, hf, hg, hγ, hX', hkeep⟩ := select_power_two_coarse D 14 hρ
    (by norm_num; linarith) hw hX hpos
  let Ds := D.select D.s f g γ
  have hmass' : O (δ ^ h₁) * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j)) := by
    let C : ENNReal := (((10 ^ 40 + 1 : ℕ) : ENNReal) ^ 14)
    have hC0 : C ≠ 0 := by simp [C]
    have hCt : C ≠ ⊤ := by simp [C]
    apply (ENNReal.mul_le_mul_iff_left hC0 hCt).mp
    calc
      (O (δ ^ h₁) * ∑ i, volume (Y i)) * C = (C * O (δ ^ h₁)) * ∑ i, volume (Y i) := by ring
      _ ≤ O (δ ^ h) * ∑ i, volume (Y i) := mul_le_mul' hselect le_rfl
      _ ≤ ∑ i, ∑ j, volume (D.W i j) := hmass
      _ ≤ C * ∑ i, ∑ j, volume (D.W i (f j)) := hkeep
      _ = _ := mul_comm _ _
  have Hs : Ds.Valid ω ζ δ h₁ ρ c x v Y 1 :=
    valid_select_coarse D hδ hδ1 hh₁ H f hf g hg γ hγ hmass'
  have hXs : X (16384 * ρ) Ds.N Ds.y Ds.w := by
    change X (16384 * ρ) N (D.y ∘ g) (D.w ∘ g)
    convert hX' using 1 <;> norm_num
  let Rs : Fin Ds.N → V ≃ₗᵢ[ℝ] V := R ∘ g
  have hRs (k : Fin Ds.N) : |Rs k (Ds.w k) 0| ≤ ρ ∧ |Rs k (Ds.w k) 1| ≤ ρ := hR (g k)
  have hclear' : ∀ i j, (Ds.W i j).Nonempty → ∀ p ∈ P Ds.a (ρ * c) c (Ds.z j) (Ds.e j),
      96 * c < dist p (x i) ∧ 96 * c < dist p (x i + v i) := by
    intro i j hi p hp
    exact hclear i (f j) hi p hp
  have hnarrow' : ∀ j j' p, Ds.γ j = Ds.γ j' → p ∈ ⋃ i, Ds.W i j → p ∈ ⋃ i, Ds.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (Rs (Ds.γ j)) (Ds.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (Rs (Ds.γ j')) (Ds.e j')) 0))) ≤ s := by
    intro j j' p he hp hp'
    have he' : D.γ (f j) = D.γ (f j') := by rw [← hγ j, ← hγ j']; exact congrArg g he
    have hh := hnarrow (f j) (f j') p he' hp hp'
    dsimp only [Ds, PrismData.select, Rs, Function.comp_apply]
    rw [hγ j, hγ j']
    exact hh
  obtain ⟨Dm, Hm, hcount, _⟩ := merge_narrow_prisms Ds hδ hδ1 hh₂ (hh.trans hh₁) hβ
    hρsmall hcsmall hδc hs hs1 has hbudget hangular hv hYI hYT Hs hXs Rs hRs hclear' hnarrow'
  apply stage_two_of_bounded_overlap Dm x v Y
    (by norm_num [geometricPacketOverlap]) hδ hδ1 hh₃ hfair hYI Hm
  intro p k
  exact_mod_cast hcount k p

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
