-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreEntryMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreEntryMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreEntryMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueBranchData
import Submission.Lib.K4NativePreparationNumerics.NativeOutputBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal BigOperators

noncomputable section

/-- Only nearby quarter-core codes enter a whole deep packet. Merging
their physical menus therefore costs a fixed number, independently of
the total number of original native cores. -/
theorem CoreEntryData.exists_deep_union_menu
    {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ Nk) (fine deep : Fin p.C) (hA : p.A deep ⊆ p.A fine)
    {e R : ℕ} {K : ℝ} (hK : 0 < K) {P : Poly} {μ : Measure Event}
    {G : Set Event} {θ : ENNReal}
    (C : CoreEntryData e R K P μ (packetNativeCubePoint Nk B p fine) G θ)
    (hsmall : p.deepBaseRadius Nk L δ₀ fine deep ≤ (K ^ R)⁻¹ / 12)
    (code : Event → Fin 4 → ℤ)
    (hphysical : ∀ i : ↥C.codes × Bool, (C.kept i).Nonempty →
      ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
        ∀ z ∈ C.kept i ∩ p.F deep, code z ∈ Menu) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 * 5832 * 2 ∧
      ∀ i : ↥C.codes × Bool, ∀ z ∈ C.kept i ∩ p.F deep, code z ∈ Menu := by
  classical
  obtain ⟨near, hnearCard, hnear⟩ := hp.exists_deep_native_quarter_core_menu hN fine deep hA
    C.center hK R hsmall
  have hex (i : ↥C.codes × Bool) :
      ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
        ∀ z ∈ C.kept i ∩ p.F deep, code z ∈ Menu := by
    by_cases hi : (C.kept i).Nonempty
    · exact hphysical i hi
    · refine ⟨∅, by simp, ?_⟩
      intro z hz
      exact (hi ⟨z, hz.1⟩).elim
  choose physical hcard hcover using hex
  let labels := near ×ˢ (Finset.univ : Finset Bool)
  let menus : (Fin 3 → ℤ) × Bool → Finset (Fin 4 → ℤ) := fun j =>
    if hj : j.1 ∈ C.codes then physical (⟨j.1, hj⟩, j.2) else ∅
  let Menu := labels.biUnion menus
  have hcardNat (j : (Fin 3 → ℤ) × Bool) : (menus j).card ≤ 108 := by
    dsimp only [menus]
    split_ifs with hj
    · exact_mod_cast hcard (⟨j.1, hj⟩, j.2)
    · simp
  have hnearNat : near.card ≤ 5832 := by exact_mod_cast hnearCard
  have hMenuNat : Menu.card ≤ 108 * 5832 * 2 := by
    calc
      Menu.card ≤ ∑ j ∈ labels, (menus j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ labels, 108 := Finset.sum_le_sum (fun j _ => hcardNat j)
      _ = near.card * 2 * 108 := by simp [labels]
      _ ≤ 108 * 5832 * 2 := by omega
  refine ⟨Menu, by exact_mod_cast hMenuNat, ?_⟩
  intro i z hz
  have hzraw := (C.subset i).1 hz.1
  have hlabel : i.1.1 ∈ near := by
    apply hnear i.1.1 (C.centers i.1.1 i.1.2).2.2 z hz.2
    have hn := (C.points i z hzraw).1
    convert hn using 1
    congr 2
    ext j
    fin_cases j <;> rfl
  apply Finset.mem_biUnion.mpr
  refine ⟨(i.1.1, i.2), Finset.mem_product.mpr ⟨hlabel, Finset.mem_univ _⟩, ?_⟩
  simpa only [menus, dite_eq_left i.1.2] using hcover i z hz

/-- All actual value bins together still have a polynomial physical
menu. No total-core count or fine-history label is added to the state. -/
theorem ValueBranchData.physical_union_menu
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hK : 2304 ≤ K)
    (menus : Fin V.count → Finset (Fin 4 → ℤ))
    (hcard : ∀ a, ((menus a).card : ℝ) ≤ 108 * 5832 * 2) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ K ^ 12 ∧
      ∀ a, menus a ⊆ Menu := by
  classical
  refine ⟨Finset.univ.biUnion menus, ?_, fun a x hx => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hx⟩⟩
  calc
    ((Finset.univ.biUnion menus).card : ℝ) ≤ ∑ a, ((menus a).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := menus))
    _ ≤ ∑ _a : Fin V.count, (108 * 5832 * 2 : ℝ) := Finset.sum_le_sum (fun a _ => hcard a)
    _ = 108 * 5832 * 2 * V.count := by simp; ring
    _ ≤ 108 * 5832 * 2 * K ^ 10 := mul_le_mul_of_nonneg_left V.count_le (by norm_num)
    _ ≤ K ^ 12 := Submission.Lib.K4NativePreparationNumerics.native_output_physical_menu_budget hK

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
