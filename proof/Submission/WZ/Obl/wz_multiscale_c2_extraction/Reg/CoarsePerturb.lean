-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.CoarsePerturb.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.Normalization

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric

/-- Finite unions add the covering constants. -/
theorem Assouad.finite_iUnion {ι : Type*} [Fintype ι]
    {d α : ℝ} {C : ι → ℝ} {B : ι → Set ℝ}
    (h : ∀ i, Assouad d α (C i) (B i)) :
    Assouad d α (∑ i, C i) (⋃ i, B i) := by
  classical
  intro r R a hdr hrR
  choose m c hc hm using fun i => h i r R a hdr hrR
  let e := Fintype.equivFin (Σ i, Fin (m i))
  refine ⟨Fintype.card (Σ i, Fin (m i)),
    (fun j => c (e.symm j).1 (e.symm j).2), ?_, ?_⟩
  · rintro u ⟨hu, huI⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc i ⟨hi, huI⟩)
    refine mem_iUnion.mpr ⟨e ⟨i, j⟩, ?_⟩
    change u ∈ closedBall (c (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2) r
    rw [e.symm_apply_apply]
    exact hj
  · calc (Fintype.card (Σ i, Fin (m i)) : ℝ) = ∑ i, (m i : ℝ) := by
          simp [Fintype.card_sigma]
      _ ≤ ∑ i, C i * (R / r) ^ α := Finset.sum_le_sum fun i _ => hm i
      _ = (∑ i, C i) * (R / r) ^ α := (Finset.sum_mul ..).symm

/-- A perturbation larger than the minimum covering scale has only a linear
loss in their ratio. Quantizing the displacement expresses it as a small
perturbation of finitely many translates. -/
theorem Assouad.perturb_mul {d α C K : ℝ} {A B : Set ℝ}
    (hd : 0 < d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hB : Assouad d α C B)
    (hAB : ∀ u ∈ A, ∃ v ∈ B, |u - v| ≤ K * d) :
    Assouad d α (18 * K * C) A := by
  classical
  let M := ⌊2 * K⌋₊ + 1
  let shift : Fin M → ℝ := fun j => ((j : ℝ) - K) * d
  let B' : Set ℝ := ⋃ j : Fin M, (fun v => v + shift j) '' B
  have hM : (M : ℝ) ≤ 3 * K := by
    have hf := Nat.floor_le (show 0 ≤ 2 * K by linarith)
    dsimp only [M]
    push_cast
    linarith
  have hB' : Assouad d α ((M : ℝ) * C) B' := by
    have hh : ∀ j : Fin M, Assouad d α C ((fun v => v + shift j) '' B) := by
      intro j
      simpa only [one_mul] using hB.affine_image (a := 1) (b := shift j) hd zero_lt_one
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Assouad.finite_iUnion hh
  have hAB' : ∀ u ∈ A, ∃ v ∈ B', |u - v| ≤ d := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := hAB u hu
    have hlo : -K ≤ (u - v) / d := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [(abs_le.mp huv).1]
    have hhi : (u - v) / d ≤ K := (div_le_iff₀ hd).mpr (abs_le.mp huv).2
    let t := (u - v) / d + K
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have htK : t ≤ 2 * K := by dsimp [t]; linarith
    let j : Fin M := ⟨⌊t⌋₊, Nat.lt_succ_of_le (Nat.floor_mono htK)⟩
    refine ⟨v + shift j, mem_iUnion.mpr ⟨j, ⟨v, hv, rfl⟩⟩, ?_⟩
    have hfloor : (j : ℝ) ≤ t := Nat.floor_le ht
    have hfloor' : t < (j : ℝ) + 1 := Nat.lt_floor_add_one t
    have hmul : ((u - v) / d) * d = u - v := div_mul_cancel₀ _ hd.ne'
    dsimp only [shift]
    apply abs_le.mpr
    constructor <;> nlinarith
  have hpert := hB'.perturb hd hα0 hα1 (mul_nonneg (Nat.cast_nonneg _) hC) hAB'
  apply hpert.mono_constant hd
  nlinarith [mul_le_mul_of_nonneg_right hM hC]

/-- A slope error of `δ^(1-κ)` costs only `18 * δ^(-κ)` in the global grains.
In particular the original minimum scale is retained. -/
theorem Assouad.projectedSlice_change_power {δ α C κ z : ℝ}
    {f g : ℝ → ℝ} {E F : Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hF : Assouad δ α C (ProjectedSlice f F z))
    (hEF : E ⊆ F) (hstrip : ∀ p ∈ E, |p 1| ≤ 1)
    (hfg : ∀ p ∈ E, |g (p 2) - f (p 2)| ≤ δ ^ (1 - κ)) :
    Assouad δ α (18 * δ ^ (-κ) * C) (ProjectedSlice g E z) := by
  apply hF.perturb_mul hδ hα0 hα1 hC
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hκ))
  have heq : δ ^ (1 - κ) = δ ^ (-κ) * δ := by
    rw [show 1 - κ = -κ + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
  simpa only [heq] using projectedSlice_perturb hEF hstrip hfg

/-- The local grains and plane field survive a coarser slope approximation. -/
theorem Grains.replace_slope_power {σ δ K K' κ : ℝ} {n : ℕ}
    {v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hK : 0 ≤ K)
    (hbudget : 18 * δ ^ (-κ) * K ≤ K')
    (h : Grains σ δ K v Y f P) (hZ : ∀ i, Z i ⊆ Y i)
    (hstrip : ∀ p ∈ ⋃ i, Z i, |p 1| ≤ 1)
    (hfg : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ ^ (1 - κ)) :
    Grains σ δ K' v Z g P := by
  obtain ⟨hglobal, hLip, hnorm, horth, hlocal⟩ := h
  have hZY : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZ
  have hp : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hκ)
  have hKK' : K ≤ K' := by nlinarith
  refine ⟨?_, hLip, (fun p hp => hnorm p (hZY hp)),
    (fun i p hp => horth i p (hZ i hp)), ?_⟩
  · intro z hz
    exact ((hglobal z hz).projectedSlice_change_power hδ hδ1 hκ
      (by linarith) (by linarith) hK hZY hstrip hfg).mono_constant hδ hbudget
  · intro ρ hδρ hρ1 p hp
    exact ((hlocal ρ hδρ hρ1 p (hZY hp)).mono_set
      (image_mono (inter_subset_inter_left _ hZY))).mono_constant
        (hδ.trans_le hδρ) hKK'

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
