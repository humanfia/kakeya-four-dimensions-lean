-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.Grains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Set Metric

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The part of a grains example that is independent of slope regularity and density. -/
def Grains (σ δ K : ℝ) {n : ℕ} (v : Fin n → Space) (Y : Fin n → Set Space)
    (f : ℝ → ℝ) (P : Space → Space) : Prop :=
  (∀ z ∈ Icc (-1 : ℝ) 1, Assouad δ (1 - σ) K (ProjectedSlice f (⋃ i, Y i) z)) ∧
  LipschitzWith 1 P ∧
  (∀ p ∈ ⋃ i, Y i, ‖P p‖ = 1) ∧
  (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
  (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ ⋃ i, Y i,
    Assouad ρ (1 - σ) K
      ((fun q => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- All the global and local grain bounds survive restriction and a scale-sized slope error.
The plane field and the tube directions are unchanged. -/
theorem Grains.replace_slope {σ δ K K' : ℝ} {n : ℕ}
    {v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hd : 0 < δ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hK : 0 ≤ K) (hK' : 6 * K ≤ K')
    (h : Grains σ δ K v Y f P)
    (hZ : ∀ i, Z i ⊆ Y i)
    (hstrip : ∀ p ∈ ⋃ i, Z i, |p 1| ≤ 1)
    (hfg : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ) :
    Grains σ δ K' v Z g P := by
  obtain ⟨hglobal, hLip, hnorm, horth, hlocal⟩ := h
  have hZY : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZ
  have hKK' : K ≤ K' := by linarith
  refine ⟨?_, hLip, (fun p hp => hnorm p (hZY hp)),
    (fun i p hp => horth i p (hZ i hp)), ?_⟩
  · intro z hz
    exact ((hglobal z hz).projectedSlice_change hd (by linarith) (by linarith) hK
      hZY hstrip hfg).mono_constant hd hK'
  · intro ρ hδρ hρ1 p hp
    exact ((hlocal ρ hδρ hρ1 p (hZY hp)).mono_set
      (image_mono (inter_subset_inter_left _ hZY))).mono_constant
        (hd.trans_le hδρ) hKK'

theorem coordinate_bound_of_subset_ball {E : Set Space} (hE : E ⊆ ball 0 1) :
    ∀ p ∈ E, |p 1| ≤ 1 := by
  intro p hp
  have hp' : ‖p‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hE hp
  have hcoord : |p 1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact hcoord.trans hp'.le

/-- The fixed multiplicity loss can be absorbed in any strictly positive exponent margin. -/
theorem exists_slope_change_cutoff {η ε : ℝ} (hηε : η < ε) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₁ →
      6 * δ ^ (-η) ≤ δ ^ (-ε) := by
  let d₁ := (1 / 6 : ℝ) ^ (ε - η)⁻¹
  have he : 0 < ε - η := sub_pos.mpr hηε
  refine ⟨d₁, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro δ hδ hδd
  have hsmall : δ ^ (ε - η) ≤ (1 / 6 : ℝ) := by
    calc δ ^ (ε - η) ≤ d₁ ^ (ε - η) := Real.rpow_le_rpow hδ.le hδd he.le
      _ = 1 / 6 := Real.rpow_inv_rpow (by norm_num) he.ne'
  have heq : δ ^ (-η) = δ ^ (ε - η) * δ ^ (-ε) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hδ.le (-ε))
  linarith

/-- A quantitative replacement lemma with exactly the power constants used by the obligation. -/
theorem Grains.replace_slope_rpow {σ η ε δ : ℝ} {n : ℕ}
    {v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hd : 0 < δ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hbudget : 6 * δ ^ (-η) ≤ δ ^ (-ε))
    (h : Grains σ δ (δ ^ (-η)) v Y f P)
    (hZ : ∀ i, Z i ⊆ Y i)
    (hball : (⋃ i, Y i) ⊆ ball 0 1)
    (hfg : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ) :
    Grains σ δ (δ ^ (-ε)) v Z g P :=
  h.replace_slope hd hσ0 hσ1 (Real.rpow_nonneg hd.le _) hbudget hZ
    (coordinate_bound_of_subset_ball ((iUnion_mono hZ).trans hball)) hfg

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
