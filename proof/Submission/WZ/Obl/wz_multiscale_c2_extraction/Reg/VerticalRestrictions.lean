-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.VerticalRestrictions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.PowerTransfer

/- Adapted from this workspace: o105/x0274 at 35a5b631a2b1dd244919169070ab09719347944a. -/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- Restricting shadings preserves all grain conditions, with a larger covering constant. -/
theorem Grains.restrict_mono {σ δ C C' : ℝ} {n : ℕ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {f : ℝ → ℝ} {P : Space → Space}
    (h : Grains σ δ C v Y f P) (hδ : 0 < δ) (hC : C ≤ C')
    (hZY : ∀ i, Z i ⊆ Y i) : Grains σ δ C' v Z f P := by
  have hsub : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZY
  refine ⟨?_, h.2.1, fun p hp => h.2.2.1 p (hsub hp),
    fun i p hp => h.2.2.2.1 i p (hZY i hp), ?_⟩
  · intro z hz
    exact Assouad.mono_constant hδ ((h.1 z hz).mono_set (projectedSlice_mono hsub z)) hC
  · intro ρ hδρ hρ1 p hp
    exact Assouad.mono_constant (hδ.trans_le hδρ)
      ((h.2.2.2.2 ρ hδρ hρ1 p (hsub hp)).mono_set
        (image_mono (inter_subset_inter_left _ hsub))) hC

/-- Deleting a subcollection of mass at most one half preserves at least one half. -/
theorem half_mass_after_deletion {I : Type*} [Fintype I]
    (w : I → ENNReal) (p : I → Prop) [DecidablePred p]
    (hfinite : ∀ i, w i ≠ ⊤)
    (hbad : ∑ i ∈ Finset.univ.filter p, w i ≤ (1 / 2 : ENNReal) * ∑ i, w i) :
    (1 / 2 : ENNReal) * ∑ i, w i ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬p i), w i := by
  classical
  have hM : (∑ i, w i) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hfinite i)
  have hhalf : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
    have hh := ENNReal.ofReal_add (p := (1 / 2 : ℝ)) (q := 1 / 2)
      (by norm_num) (by norm_num)
    norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hh
    exact hh.symm
  apply (ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hM)).mp
  calc
    (1 / 2 : ENNReal) * (∑ i, w i) + (1 / 2 : ENNReal) * (∑ i, w i)
        = ∑ i, w i := by rw [← add_mul, hhalf, one_mul]
    _ = (∑ i ∈ Finset.univ.filter p, w i) +
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i), w i :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ p w).symm
    _ ≤ _ := add_le_add hbad le_rfl


end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
