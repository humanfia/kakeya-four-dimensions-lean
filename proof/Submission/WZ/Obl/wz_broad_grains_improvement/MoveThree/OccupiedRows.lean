-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.OccupiedRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/OccupiedRows.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/OccupiedRows.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.VariableIncidenceAssembly

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory

/-- Empty candidate labels may be discarded without changing any column union
or any column mass. The enumeration retains each occupied label exactly once. -/
theorem nonempty_row_reindex {κ ι : Type*} [Fintype κ] [Fintype ι]
    (W : κ → ι → Set V) :
    ∃ (K : ℕ) (idx : Fin K → κ), Function.Injective idx ∧
      (∀ k, (⋃ i, W (idx k) i).Nonempty) ∧
      (∀ k, (⋃ i, W k i).Nonempty → ∃ l, idx l = k) ∧
      (∀ i, (⋃ k, W (idx k) i) = ⋃ k, W k i) ∧
      (∀ i, (∑ k, μ (W (idx k) i)) = ∑ k, μ (W k i)) := by
  classical
  let Q := Finset.univ.filter (fun k => (⋃ i, W k i).Nonempty)
  let idx : Fin Q.card → κ := fun k => (Q.equivFin.symm k).1
  have hidx (k : Fin Q.card) : idx k ∈ Q := (Q.equivFin.symm k).2
  have hmem (k : κ) : k ∈ Q ↔ (⋃ i, W k i).Nonempty := by simp [Q]
  have hsurj (k : κ) (hk : (⋃ i, W k i).Nonempty) : ∃ l, idx l = k := by
    refine ⟨Q.equivFin ⟨k, (hmem k).mpr hk⟩, ?_⟩
    simp [idx]
  refine ⟨Q.card, idx, ?_, ?_, hsurj, ?_, ?_⟩
  · exact fun k l he => Q.equivFin.symm.injective (Subtype.ext he)
  · exact fun k => (hmem (idx k)).mp (hidx k)
  · intro i
    ext p
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨idx k, hk⟩
    · intro hp
      obtain ⟨k, hk⟩ := mem_iUnion.mp hp
      obtain ⟨l, hl⟩ := hsurj k ⟨p, mem_iUnion.mpr ⟨i, hk⟩⟩
      exact mem_iUnion.mpr ⟨l, hl.symm ▸ hk⟩
  · intro i
    calc
      (∑ k, μ (W (idx k) i)) = ∑ k ∈ Q, μ (W k i) := by
        rw [← Finset.sum_coe_sort Q (fun k => μ (W k i))]
        exact Equiv.sum_comp Q.equivFin.symm (fun k => μ (W k.1 i))
      _ = ∑ k, μ (W k i) := by
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro k _ hk
        have hW : W k i = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          exact hk ((hmem k).mpr ⟨p, mem_iUnion.mpr ⟨i, hp⟩⟩)
        simp [hW, μ]


open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale (dyExp)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

/-- The variable-width assembly only requires geometric and density data
on occupied candidates; empty labels contribute no incidence mass. -/
theorem variable_incidence_prisms_of_occupied_rows {κ : Type*} [Fintype κ]
    {ω ζ δ h h' ρ ρ₀ a c b g m t s lam B C₀ : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (W : κ → Fin L → Set V) (z' : κ → V) (e' : κ → V ≃ₗᵢ[ℝ] V)
    (aRow bRow : κ → ℝ) (ν : κ → Fin L → V) (R : κ → V ≃ₗᵢ[ℝ] V) (θ : κ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B) (hm : 0 ≤ m) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t)
    (hv : ∀ i, ‖v i‖ = 1) (hTI : ∀ i, T δ (x i) (v i) ⊆ I)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hdim : ∀ k, (⋃ j, W k j).Nonempty → δ ≤ aRow k ∧ aRow k ≤ bRow k ∧ bRow k ≤ c)
    (hgrow : ∀ k, (⋃ j, W k j).Nonempty → ρ₀ * c ≤ bRow k)
    (hWm : ∀ k j, MeasurableSet (W k j)) (hWH : ∀ k j, W k j ⊆ Hs j)
    (hWdisj : ∀ j, Pairwise fun k k' => Disjoint (W k j) (W k' j))
    (hWU : ∀ k j, W k j ⊆ P (aRow k) (bRow k) c (z' k) (e' k))
    (hretain : O t * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W k j))
    (hpos : 0 < ∑ k, ∑ j, μ (W k j))
    (hclassBudget : (((dyExp 1 δ + 1) ^ 2 : ℕ) : ℝ) ≤ δ ^ (-s))
    (hmassBudget : δ ^ h' ≤ (t * δ ^ s / 2) * δ ^ h)
    (hdense : ∀ k, (⋃ j, W k j).Nonempty → O lam * μ (P (aRow k) (bRow k) c (z' k) (e' k)) ≤ μ (⋃ j, W k j))
    (hdensityBudget : 4 * δ ^ h' ≤ lam)
    (hcross : ∀ i ∈ S, ∀ k j, f i = γ j → (Z i ∩ W k j).Nonempty →
      Crosses δ (aRow k) (bRow k) c (x i) (v i) (z' k) (e' k))
    (hθ : ∀ k, (⋃ j, W k j).Nonempty → 0 < θ k)
    (hclose : ∀ k j, (W k j).Nonempty →
      pd (ν k j) (R k (boxAxis (e j) 2)) ≤ C₀ * ρ)
    (haxis : ∀ k p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W k j ∧ pd (ν k j) u ≤ r} ≤
        B * (r / θ k) ^ (ω * ζ / 100) * q L {j | p ∈ W k j})
    (hbroadBudget : ∀ k, (⋃ j, W k j).Nonempty → 2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100) *
      (2 * bRow k / (c * θ k)) ^ (ω * ζ / 100) ≤ δ ^ (-h')) :
    ∃ ρ', ρ₀ ≤ ρ' ∧
      WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ' c n x v Y 0 := by
  classical
  obtain ⟨K, idx, hinj, hocc, _, _, hsumcol⟩ := nonempty_row_reindex W
  have hsum : (∑ k, ∑ j, μ (W (idx k) j)) = ∑ k, ∑ j, μ (W k j) := by
    calc
      _ = ∑ j, ∑ k, μ (W (idx k) j) := Finset.sum_comm
      _ = ∑ j, ∑ k, μ (W k j) := by simp_rw [hsumcol]
      _ = _ := Finset.sum_comm
  exact variable_incidence_prisms_of_grain_rows (fun k => W (idx k))
    (fun k => z' (idx k)) (fun k => e' (idx k)) (fun k => aRow (idx k))
    (fun k => bRow (idx k)) (fun k => ν (idx k)) (fun k => R (idx k))
    (fun k => θ (idx k)) hδ hδ1 hh hδρ hβ hB hm hC₀ ht hv hTI hC hbr hHB
    (fun k => hdim (idx k) (hocc k)) (fun k => hgrow (idx k) (hocc k))
    (fun k => hWm (idx k)) (fun k => hWH (idx k))
    (fun j k k' hne => hWdisj j (hinj.ne hne)) (fun k => hWU (idx k))
    (by rwa [hsum]) (by rwa [hsum]) hclassBudget hmassBudget
    (fun k => hdense (idx k) (hocc k)) hdensityBudget
    (fun i hi k => hcross i hi (idx k)) (fun k => hθ (idx k) (hocc k))
    (fun k => hclose (idx k)) (fun k => haxis (idx k))
    (fun k => hbroadBudget (idx k) (hocc k))

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
