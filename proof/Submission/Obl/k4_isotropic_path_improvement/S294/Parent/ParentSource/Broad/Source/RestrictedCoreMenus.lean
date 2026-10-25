-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RestrictedCoreMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RestrictedCoreMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/RestrictedCoreMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryMenus

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

/-- The nearby-core menu also merges signals on an arbitrary later
source. The source restriction costs no extra geometric labels. -/
theorem CoreEntryData.exists_deep_restricted_union_menu
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B profile κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ N) (fine deep : Fin p.C) (hA : p.A deep⊆p.A fine)
    {e R : ℕ} {K : ℝ} (hK : 0 < K) {P : Poly} {μ : Measure Event}
    {G : Set Event} {θ : ENNReal}
    (C : CoreEntryData e R K P μ (packetNativeCubePoint N B p fine) G θ)
    (hsmall : p.deepBaseRadius N L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (source : Set Event) (code : Event → Fin 4 → ℤ)
    (hphysical : ∀ i : ↥C.codes × Bool,
      ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card:ℝ) ≤ 108 ∧
        ∀ z∈source∩C.kept i∩p.F deep, code z∈Menu) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card:ℝ) ≤ 108*5832*2 ∧
      ∀ i : ↥C.codes × Bool, ∀ z∈source∩C.kept i∩p.F deep, code z∈Menu := by
  classical
  obtain ⟨near,hnearCard,hnear⟩ := hp.exists_deep_native_quarter_core_menu hN fine deep hA
    C.center hK R hsmall
  choose physical hcard hcover using hphysical
  let labels := near ×ˢ (Finset.univ : Finset Bool)
  let menus : (Fin 3 → ℤ) × Bool → Finset (Fin 4 → ℤ) := fun j =>
    if hj : j.1∈C.codes then physical (⟨j.1,hj⟩,j.2) else ∅
  let Menu := labels.biUnion menus
  have hcardNat (j : (Fin 3 → ℤ) × Bool) : (menus j).card ≤ 108 := by
    dsimp only [menus]
    split_ifs with hj
    · exact_mod_cast hcard (⟨j.1,hj⟩,j.2)
    · simp
  have hnearNat : near.card ≤ 5832 := by exact_mod_cast hnearCard
  have hMenuNat : Menu.card ≤ 108*5832*2 := by
    calc
      Menu.card ≤ ∑ j∈labels, (menus j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j∈labels, 108 := Finset.sum_le_sum (fun j _ => hcardNat j)
      _ = near.card*2*108 := by simp [labels]
      _ ≤ 108*5832*2 := by omega
  refine ⟨Menu,by exact_mod_cast hMenuNat,?_⟩
  intro i z hz
  have hzraw := (C.subset i).1 hz.1.2
  have hlabel : i.1.1∈near := by
    apply hnear i.1.1 (C.centers i.1.1 i.1.2).2.2 z hz.2
    have hn := (C.points i z hzraw).1
    convert hn using 1
    congr 2
    ext j
    fin_cases j <;> rfl
  apply Finset.mem_biUnion.mpr
  refine ⟨(i.1.1,i.2),Finset.mem_product.mpr ⟨hlabel,Finset.mem_univ _⟩,?_⟩
  simpa only [menus,dite_eq_left i.1.2] using hcover i z hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
