-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridSmoothing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridSelection
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.DifferenceExtension
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.LinearityIteration

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

/-- A finite sequence of grid-affine approximants yields a smooth approximation
on a compact retained set. The lost height mass and all global C2 bounds are
explicit. In particular, no compatibility of the grids is assumed. -/
theorem exists_smooth_grid_approximation : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (μ : Measure ℝ) (L : ℝ) (D : Set ℝ) (f : ℝ → ℝ)
      (A : Fin (N + 1) → ℝ → ℝ) (h E : Fin (N + 1) → ℝ) (a : Fin N → ℝ) (δ : ℝ),
      0 ≤ L →
      (∀ l u : ℝ, μ (Icc l u) ≤ ENNReal.ofReal L * ENNReal.ofReal (u - l)) →
      IsCompact D → D ⊆ Icc (-1 : ℝ) 1 →
      (∀ k, 0 < h k) → (∀ k, h k ≤ 1) → (∀ k, 0 ≤ E k) →
      (∀ k, 0 < a k) → (∀ k, a k ≤ 1) →
      (∀ k, AffineOnGrid (h k) (A k)) → (∀ z, A 0 z = 0) →
      (∀ k z, z ∈ D → |f z - A k z| ≤ E k) →
      (∀ z ∈ D, |f z - A (Fin.last N) z| ≤ δ) →
      ∃ (D' : Set ℝ) (g : ℝ → ℝ), D' ⊆ D ∧ IsCompact D' ∧
        μ D ≤ μ D' + ∑ k : Fin N,
          ENNReal.ofReal (55 * L * (a k / h k.succ + h k.succ / h k.castSucc)) ∧
        ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ z ∈ D', |f z - g z| ≤ δ) ∧
        (∀ z, |g z| ≤ C * ∑ k : Fin N, (E k.succ + E k.castSucc) / a k) ∧
        (∀ z, |deriv g z| ≤ C * ∑ k : Fin N, (E k.succ + E k.castSucc) / a k) ∧
        (∀ z, |deriv (deriv g) z| ≤
          C * ∑ k : Fin N, (E k.succ + E k.castSucc) / (a k) ^ 2) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_difference_extension
  refine ⟨C, hC, ?_⟩
  intro N μ L D f A h E a δ hL hμ hD hDbox hh hh1 hE ha ha1 hgrid hzero hfit hfinal
  classical
  let I : Fin N → Type := fun k => LongGridIndex D (h k.succ) (h k.castSucc) (a k)
  let S : ∀ k, I k → Set ℝ := fun k => longGridSample D (h k.succ) (h k.castSucc) (a k)
  let U : Fin N → Set ℝ := fun k => ⋃ i, S k i
  let D' := D ∩ ⋂ k, U k
  have hSc : ∀ k i, IsCompact (S k i) := fun k i => longGridSample_compact hD _ _ _ i
  have hSne : ∀ k i, (S k i).Nonempty := fun k i => longGridSample_nonempty (ha k) i
  have hSD : ∀ k i, S k i ⊆ D := fun k i => longGridSample_subset i
  have hD'sub : D' ⊆ D := inter_subset_left
  have hD'c : IsCompact D' :=
    hD.inter_right (isClosed_iInter (fun k => (isCompact_iUnion (hSc k)).isClosed))
  have hdata : ∀ k i, ∃ b s : ℝ,
      ∀ z ∈ Icc (sInf (S k i)) (sSup (S k i)),
        A k.succ z - A k.castSucc z = b + s * z := by
    intro k i
    obtain ⟨m, hm⟩ := longGridSample_in_cells hD (hh k.succ) (hh k.castSucc) (ha k) i
    obtain ⟨b₁, s₁, h₁⟩ := hgrid k.succ i.1.1
    obtain ⟨b₀, s₀, h₀⟩ := hgrid k.castSucc m
    refine ⟨b₁ - b₀, s₁ - s₀, ?_⟩
    intro z hz
    rw [h₁ z (hm hz).1, h₀ z (hm hz).2]
    ring
  choose b s hdiff using hdata
  have herr : ∀ k i z, z ∈ S k i →
      |A k.succ z - A k.castSucc z| ≤ E k.succ + E k.castSucc := by
    intro k i z hz
    have hzD := hSD k i hz
    calc
      |A k.succ z - A k.castSucc z| ≤ |A k.succ z - f z| + |f z - A k.castSucc z| :=
        abs_sub_le _ _ _
      _ ≤ E k.succ + E k.castSucc :=
        add_le_add (by simpa only [abs_sub_comm] using hfit k.succ z hzD)
          (hfit k.castSucc z hzD)
  have hcover : ∀ z ∈ D', ∀ k, ∃ i, z ∈ Icc (sInf (S k i)) (sSup (S k i)) := by
    intro z hz k
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((mem_iInter.mp hz.2) k)
    exact ⟨i, subset_Icc_csInf_csSup (hSc k i).bddBelow (hSc k i).bddAbove hi⟩
  obtain ⟨g, hg, hgf, hg₀, hg₁, hg₂⟩ :=
    hext N I A S b s a (fun k => E k.succ + E k.castSucc) D' f δ
      ha ha1 (fun k => add_nonneg (hE _) (hE _)) hSc hSne
      (fun k i => (hSD k i).trans hDbox)
      (fun k i => longGridSample_length i)
      (fun k => longGridSample_separated hD (hh k.succ) (ha k))
      hdiff herr hzero hcover (fun z hz => hfinal z hz.1)
  refine ⟨D', g, hD'sub, hD'c, ?_, hg, hgf, hg₀, hg₁, hg₂⟩
  apply measure_simultaneous_height_selection μ D U
  intro k
  exact longGridSamples_mass_error hL hμ hD hDbox
    (hh k.succ) (hh1 k.succ) (hh k.castSucc) (hh1 k.castSucc) (ha k).le

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
