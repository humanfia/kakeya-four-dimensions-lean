-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RetainedAncestorSignalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RetainedAncestorSignalMenus.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
/- Adapted from this tree's RetainedAnisotropicMenus.lean. The original
 o265/session x0943 attribution and earlier credits are preserved below. -/
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/RetainedAnisotropicMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreAncestorSignalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Actual earlier raw native cores give a short menu for R_root/aChild
on each whole later history, including all value bins and core signs.
Both the base chart and signal units are those of the independently
chosen child. No later-history mass floor or extra cut is used. -/
theorem ValueBranchData.exists_deep_ancestor_signal_source_menu
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (root child deep : Fin p.C) (hγ : p.γ b = p.γ root)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev root)))
    (hFineOld : p.F b ⊆ p.F root)
    (hADeepFine : p.A deep ⊆ p.A b)
    (hFDeepFine : p.F deep ⊆ p.F b)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : p.unshearedDeepRadius child deep ≤ baseMesh)
    (hheightSmall :
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*
        (2 * (K ^ 14 * (K ^ 6)⁻¹ *
          (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev root)))) +
          ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep)) ≤ hidden)
    (hcoreSmall : p.deepBaseRadius (d.N k) d.L δ₀ b deep ≤ (K ^ R)⁻¹ / 12) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ K ^ 12 ∧
      ∀ z ∈ V.coreRetained cores (p.γ root) ∩ p.F deep,
        jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z) ∈ Menu := by
  classical
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hKpos : 0 < K := by linarith
  let I := {v : V.ActiveValue // v.1.1 = b}
  letI : Fintype I := Fintype.ofFinite I
  have hI : Fintype.card I ≤ V.count := by
    have hinj : Function.Injective (fun v : I => v.1.1.2) := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (v.2.trans w.2.symm) h
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  have hentry (v : I) : ∃ Menu : Finset (Fin 4 → ℤ),
      (Menu.card : ℝ) ≤ 108 * 5832 * 2 ∧
      ∀ i, ∀ z ∈ (cores v.1).kept i ∩ p.F deep,
        jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z) ∈ Menu := by
    let C := cores v.1
    have hvb : v.1.1.1 = b := v.2
    have hBv : 0 < d.B k (p.γ v.1.1.1) := by simpa only [hvb] using hB
    have hγv : p.γ v.1.1.1 = p.γ root := by simpa only [hvb] using hγ
    have hwv : δ (d.N k) (p.r (p.lev v.1.1.1)) ≤ δ (d.N k) (p.r (p.lev root)) := by
      simpa only [hvb] using hwidth
    have hFv : p.F v.1.1.1 ⊆ p.F root := by simpa only [hvb] using hFineOld
    apply CoreEntryData.exists_deep_union_menu hp hN v.1.1.1 deep
      (by simpa only [hvb] using hADeepFine) hKpos C
      (by simpa only [hvb] using hcoreSmall) (fun z => jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z))
    intro i hi
    exact CoreEntryData.exists_actual_deep_ancestor_signal_menu V Q hpure hd hp
      hHE hHbase hK hmax hpower hκK v.1.1.1 v.1.2.1 hr hrL hBv v.1.1.2 C i hi hD hjets
      root child deep hγv hwv hFv (by simpa only [hvb] using hADeepFine)
      hbase hhidden hbaseSmall (by simpa only [hvb] using hheightSmall)
      (C.kept i ∩ p.F deep) (fun z hz => (C.subset i).1 hz.1) inter_subset_right
  choose F hF hcover using hentry
  let Menu := Finset.univ.biUnion F
  have hcard : (Menu.card : ℝ) ≤ ∑ v : I, ((F v).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  refine ⟨Menu, ?_, ?_⟩
  · calc
      _ ≤ ∑ _v : I, (108 * 5832 * 2 : ℝ) :=
        hcard.trans (Finset.sum_le_sum (fun v _ => hF v))
      _ = (108 * 5832 * 2 : ℝ) * Fintype.card I := by simp; ring
      _ ≤ (108 * 5832 * 2 : ℝ) * V.count :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hI) (by norm_num)
      _ ≤ (108 * 5832 * 2 : ℝ) * K ^ 10 := mul_le_mul_of_nonneg_left V.count_le (by norm_num)
      _ ≤ K ^ 12 := Submission.Lib.K4NativePreparationNumerics.native_output_physical_menu_budget hK
  · intro z hz
    obtain ⟨hzres, hzunion⟩ := hz.1
    obtain ⟨v, hv⟩ := mem_iUnion.mp hzunion
    by_cases hγv : p.γ v.1.1 = p.γ root
    · rw [ite_eq_left hγv] at hv
      obtain ⟨hzinner, hzkept⟩ := hv
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hzkept
      have hzbase := hHbase _ (V.residual_subset _ hzres)
      have hzfine : z ∈ p.F v.1.1 := ((V.subset v.1.1 v.1.2).2
        ((V.subset v.1.1 v.1.2).1 hzinner)).2
      have heq := Q.base_packet_unique (p.γ root) z hzbase v.1.1 b
        (v.2.1.trans hb.symm) hγv hγ hzfine (hFDeepFine hz.2)
      let v' : I := ⟨v, heq⟩
      exact Finset.mem_biUnion.mpr ⟨v', Finset.mem_univ _, hcover v' i z ⟨hzi, hz.2⟩⟩
    · rw [ite_eq_right hγv] at hv
      exact hv.elim

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
