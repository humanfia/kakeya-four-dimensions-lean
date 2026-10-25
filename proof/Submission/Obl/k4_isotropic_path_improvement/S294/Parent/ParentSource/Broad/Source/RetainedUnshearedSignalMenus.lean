-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RetainedUnshearedSignalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RetainedUnshearedSignalMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/RetainedUnshearedSignalMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RestrictedCoreMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- A signal controlled on the actual retained value/core entries has
a short unsheared menu on every resolved whole deeper packet. All value
bins and nearby core signs are merged; later selection adds no labels. -/
theorem ValueBranchData.exists_deep_retained_unsheared_signal_menu
    (hHbase : ∀ w, H w⊆Q.base w) (hK : 2304 ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    (b : Fin p.C) (hb : p.lev b=mid)
    (old deep : Fin p.C) (hγ : p.γ b=p.γ old)
    (hADeepFine : p.A deep⊆p.A b) (hFDeepFine : p.F deep⊆p.F b)
    (source : Set Event) (hsource : source⊆V.coreRetained cores (p.γ old))
    (signal : Event → ℝ) {additive Lip base hidden : ℝ} (hLip : 0 ≤ Lip)
    (hbase : 0 < base) (hhidden : 0 < hidden)
    (hbaseSmall : p.unshearedDeepRadius old deep ≤ base)
    (hheightSmall : additive+Lip*(6*p.unshearedDeepRadius old deep) ≤ hidden)
    (hcoreSmall : p.deepBaseRadius (d.N k) d.L δ₀ b deep ≤ (K^R)⁻¹/12)
    (hpair : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      ∀ z∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
      ∀ z'∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
        |signal z-signal z'| ≤ additive+Lip*
          ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card:ℝ) ≤ K^12 ∧
      ∀ z∈source∩p.F deep,
        jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈Menu := by
  classical
  have hN : 1 ≤ d.N k := (by norm_num : (1:ℝ) ≤ 2).trans (hd.1 k)
  have hKpos : 0 < K := by linarith
  let I := {v : V.ActiveValue // v.1.1=b}
  letI : Fintype I := Fintype.ofFinite I
  have hI : Fintype.card I ≤ V.count := by
    have hinj : Function.Injective (fun v : I => v.1.1.2) := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (v.2.trans w.2.symm) h
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  let code := fun z => jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)
  have hentry (v : I) : ∃ Menu : Finset (Fin 4 → ℤ),
      (Menu.card:ℝ) ≤ 108*5832*2 ∧
      ∀ ci, ∀ z∈source∩V.inner v.1.1.1 v.1.1.2∩(cores v.1).kept ci∩p.F deep,
        code z∈Menu := by
    let C := cores v.1
    apply C.exists_deep_restricted_union_menu hp hN v.1.1.1 deep
      (by simpa only [v.2] using hADeepFine) hKpos
      (by simpa only [v.2] using hcoreSmall)
      (source∩V.inner v.1.1.1 v.1.1.2) code
    intro ci
    apply hp.exists_deep_unsheared_signal_menu old deep hbase hhidden hbaseSmall signal
      (source∩V.inner v.1.1.1 v.1.1.2∩C.kept ci∩p.F deep) inter_subset_right
    intro z hz z' hz'
    have hh := hpair v.1 ci ((congrArg p.γ v.2).trans hγ)
      z ⟨hz.1.1.1,⟨hz.1.1.2,hz.1.2⟩⟩ z' ⟨hz'.1.1.1,⟨hz'.1.1.2,hz'.1.2⟩⟩
    exact hh.trans ((add_le_add (le_refl additive) (mul_le_mul_of_nonneg_left
      (hp.deep_unsheared_base_diameter old deep z hz.2 z' hz'.2) hLip)).trans hheightSmall)
  choose F hF hcover using hentry
  let Menu := Finset.univ.biUnion F
  have hcard : (Menu.card:ℝ) ≤ ∑ v : I, ((F v).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  refine ⟨Menu,?_,?_⟩
  · calc
      _ ≤ ∑ _v : I, (108*5832*2:ℝ) := hcard.trans (Finset.sum_le_sum (fun v _ => hF v))
      _ = (108*5832*2:ℝ)*Fintype.card I := by simp; ring
      _ ≤ (108*5832*2:ℝ)*V.count :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hI) (by norm_num)
      _ ≤ (108*5832*2:ℝ)*K^10 := mul_le_mul_of_nonneg_left V.count_le (by norm_num)
      _ ≤ K^12 := Submission.Lib.K4NativePreparationNumerics.native_output_physical_menu_budget hK
  · intro z hz
    obtain ⟨hzres,hzunion⟩ := hsource hz.1
    obtain ⟨v,hv⟩ := mem_iUnion.mp hzunion
    by_cases hγv : p.γ v.1.1=p.γ old
    · rw [ite_eq_left hγv] at hv
      obtain ⟨hzinner,hzkept⟩ := hv
      obtain ⟨ci,hzi⟩ := mem_iUnion.mp hzkept
      have hzbase := hHbase _ (V.residual_subset _ hzres)
      have hzfine : z∈p.F v.1.1 :=
        ((V.subset v.1.1 v.1.2).2 ((V.subset v.1.1 v.1.2).1 hzinner)).2
      have heq := Q.base_packet_unique (p.γ old) z hzbase v.1.1 b
        (v.2.1.trans hb.symm) hγv hγ hzfine (hFDeepFine hz.2)
      let v' : I := ⟨v,heq⟩
      exact Finset.mem_biUnion.mpr ⟨v',Finset.mem_univ _,
        hcover v' ci z ⟨⟨⟨hz.1,hzinner⟩,hzi⟩,hz.2⟩⟩
    · rw [ite_eq_right hγv] at hv
      exact hv.elim

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
