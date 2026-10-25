-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.IncidenceGrainAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/IncidenceGrainAssembly.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/IncidenceGrainAssembly.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainFinePieces
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

/-- All original tubes in the unit ball share a harmless auxiliary tube
cover for stage zero of the incidence-prism predicate. -/
theorem unit_ball_subset_auxiliary_tube (u : V) : I ⊆ T 1 0 u := by
  intro p hp
  apply Metric.mem_thickening_iff.mpr
  exact ⟨0, left_mem_segment ℝ 0 (0 + u), hp⟩

/-- Row refinements with common candidate dimensions assemble the accepted
per-incidence prism predicate. Crossing is needed only for incidences that
belong to that candidate, and no global ownership hypothesis occurs. -/
theorem incidence_prisms_of_grain_rows
    {ω ζ δ h h' ρ ρ' a a' c b g m t B C₀ : ℝ} {n N L K : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (W : Fin K → Fin L → Set V) (z' : Fin K → V) (e' : Fin K → V ≃ₗᵢ[ℝ] V)
    (ν : Fin K → Fin L → V) (R : Fin K → V ≃ₗᵢ[ℝ] V) (θ : Fin K → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hρ' : 0 < ρ') (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B)
    (hm : 0 ≤ m) (hC₀ : 0 ≤ C₀) (ht : 0 ≤ t)
    (hv : ∀ i, ‖v i‖ = 1) (hTI : ∀ i, T δ (x i) (v i) ⊆ I)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hδa' : δ ≤ a') (ha'ρ' : a' ≤ ρ' * c) (hρ'c : ρ' * c ≤ c)
    (hWm : ∀ k j, MeasurableSet (W k j)) (hWH : ∀ k j, W k j ⊆ Hs j)
    (hWdisj : ∀ j, Pairwise fun k k' => Disjoint (W k j) (W k' j))
    (hWU : ∀ k j, W k j ⊆ P a' (ρ' * c) c (z' k) (e' k))
    (hretain : O t * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W k j))
    (hmassBudget : δ ^ h' ≤ (t / 2) * δ ^ h)
    (hdense : ∀ k, O (δ ^ h') * μ (P a' (ρ' * c) c (z' k) (e' k)) ≤ μ (⋃ j, W k j))
    (hcross : ∀ i ∈ S, ∀ k j, f i = γ j → (Z i ∩ W k j).Nonempty →
      Crosses δ a' (ρ' * c) c (x i) (v i) (z' k) (e' k))
    (hθ : ∀ k, 0 < θ k)
    (hclose : ∀ k j, (W k j).Nonempty →
      pd (ν k j) (R k (boxAxis (e j) 2)) ≤ C₀ * ρ)
    (haxis : ∀ k p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W k j ∧ pd (ν k j) u ≤ r} ≤
        B * (r / θ k) ^ (ω * ζ / 100) * q L {j | p ∈ W k j})
    (hbroadBudget : ∀ k, 2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100) *
      (ρ' / θ k) ^ (ω * ζ / 100) ≤ δ ^ (-h')) :
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ' c n x v Y 0 := by
  classical
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  obtain ⟨hFm, hFdisj, hFmass, _, hFunion⟩ := labelled_grainFineRefinement
    hHB (fun i => (hC.1 i).1) hsupport hbr W hWm hWH hWdisj ht hretain
  let F := fun i k => grainFineRefinement S Z f (W k) γ i
  let u : V := EuclideanSpace.single 2 1
  have hu : ‖u‖ = 1 := by simp [u]
  refine ⟨a', 1, K, 1, z', e', F, (fun _ => 0), (fun _ => u), (fun _ => 0),
    hδa', ha'ρ', hρ'c, hHB.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, (fun _ => hu),
    (by omega), (by omega)⟩
  · intro i k
    refine ⟨(hFm k i).1, ?_, fun k' hne => hFdisj i hne⟩
    intro p hp
    refine ⟨(hC.1 i).2.1 ((hFm k i).2 hp), ?_⟩
    obtain ⟨_, _, j, _, hj⟩ := (mem_grainFineRefinement S Z f (W k) γ i p).mp hp
    exact hWU k j hj
  · change O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i, ∑ k, μ (F i k)
    calc
      _ ≤ (O (t / 2) * O (δ ^ h)) * ∑ i, μ (Y i) := by
        apply mul_le_mul' _ le_rfl
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ t / 2)]
        exact ENNReal.ofReal_le_ofReal hmassBudget
      _ = O (t / 2) * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O (t / 2) * ∑ i, μ (Z i) :=
        mul_le_mul' le_rfl (hC.2.1.trans_eq (Clear.sum_supported hsupport))
      _ ≤ ∑ k, ∑ i, μ (F i k) := hFmass
      _ = _ := Finset.sum_comm
  · intro k
    change O (δ ^ h') * μ (P a' (ρ' * c) c (z' k) (e' k)) ≤
      μ (⋃ i, grainFineRefinement S Z f (W k) γ i)
    rw [hFunion]
    exact hdense k
  · intro i k hne
    refine ⟨(hTI i).trans (unit_ball_subset_auxiliary_tube u), ?_⟩
    obtain ⟨p, hp⟩ := hne
    obtain ⟨hi, hpi, j, hj, hpj⟩ := (mem_grainFineRefinement S Z f (W k) γ i p).mp hp
    exact hcross i hi k j hj.symm ⟨p, hpi, hpj⟩
  · intro k p u₀ r hu₀ hr _
    have H := grain_refinement_fine_broad_in_frame (R k) hδ hδ1 hh hδρ (hθ k) hβ hB hm
      hC₀ hv hC hbr hHB (hWH k) (hclose k) (haxis k) p u₀ r hu₀ hr
    have hr0 : 0 ≤ r := hδ.le.trans hr
    have he : (r / θ k) ^ (ω * ζ / 100) =
        (ρ' / θ k) ^ (ω * ζ / 100) * (r / ρ') ^ (ω * ζ / 100) := by
      rw [← Real.mul_rpow (div_nonneg hρ'.le (hθ k).le) (div_nonneg hr0 hρ'.le)]
      congr 1
      field_simp
    rw [he] at H
    have H' : q n {i | p ∈ F i k ∧ pd (v i) u₀ ≤ r} ≤
        (2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100) *
          (ρ' / θ k) ^ (ω * ζ / 100)) * (r / ρ') ^ (ω * ζ / 100) *
            q n {i | p ∈ F i k} := by
      convert H using 1
      ring
    exact H'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbroadBudget k)
        (Real.rpow_nonneg (div_nonneg hr0 hρ'.le) _)) (Nat.cast_nonneg _))
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
