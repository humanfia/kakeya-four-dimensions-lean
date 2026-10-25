-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.VariableIncidenceAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/VariableIncidenceAssembly.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/VariableIncidenceAssembly.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.IncidenceGrainAssembly
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismWidthClasses

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale (dyExp)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

/-- Finite candidate rows may have different transverse dimensions. A pair
of width classes makes them common with a subpower mass loss, preserves the
long length, and retains every lower bound for the angular width. -/
theorem variable_incidence_prisms_of_grain_rows {κ : Type*} [Fintype κ]
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
    (hdim : ∀ k, δ ≤ aRow k ∧ aRow k ≤ bRow k ∧ bRow k ≤ c)
    (hgrow : ∀ k, ρ₀ * c ≤ bRow k)
    (hWm : ∀ k j, MeasurableSet (W k j)) (hWH : ∀ k j, W k j ⊆ Hs j)
    (hWdisj : ∀ j, Pairwise fun k k' => Disjoint (W k j) (W k' j))
    (hWU : ∀ k j, W k j ⊆ P (aRow k) (bRow k) c (z' k) (e' k))
    (hretain : O t * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W k j))
    (hpos : 0 < ∑ k, ∑ j, μ (W k j))
    (hclassBudget : (((dyExp 1 δ + 1) ^ 2 : ℕ) : ℝ) ≤ δ ^ (-s))
    (hmassBudget : δ ^ h' ≤ (t * δ ^ s / 2) * δ ^ h)
    (hdense : ∀ k, O lam * μ (P (aRow k) (bRow k) c (z' k) (e' k)) ≤ μ (⋃ j, W k j))
    (hdensityBudget : 4 * δ ^ h' ≤ lam)
    (hcross : ∀ i ∈ S, ∀ k j, f i = γ j → (Z i ∩ W k j).Nonempty →
      Crosses δ (aRow k) (bRow k) c (x i) (v i) (z' k) (e' k))
    (hθ : ∀ k, 0 < θ k)
    (hclose : ∀ k j, (W k j).Nonempty →
      pd (ν k j) (R k (boxAxis (e j) 2)) ≤ C₀ * ρ)
    (haxis : ∀ k p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W k j ∧ pd (ν k j) u ≤ r} ≤
        B * (r / θ k) ^ (ω * ζ / 100) * q L {j | p ∈ W k j})
    (hbroadBudget : ∀ k, 2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100) *
      (2 * bRow k / (c * θ k)) ^ (ω * ζ / 100) ≤ δ ^ (-h')) :
    ∃ ρ', ρ₀ ≤ ρ' ∧
      WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ' c n x v Y 0 := by
  classical
  have hc : 0 < c := hδ.trans_le ((hHB.1.trans hHB.2.1).trans hHB.2.2.1)
  obtain ⟨a', b', Q, hQ, hδa', ha'b', hb'c, hround, hmassQ⟩ :=
    select_prism_width_class hδ hHB.2.2.2.1 aRow bRow (fun k => ∑ j, μ (W k j)) hdim hpos
  let idx : Fin Q.card → κ := fun k => (Q.equivFin.symm k).1
  have hidx (k) : idx k ∈ Q := (Q.equivFin.symm k).2
  have hinj : Function.Injective idx := fun k k' he =>
    Q.equivFin.symm.injective (Subtype.ext he)
  have hsum : (∑ k, ∑ j, μ (W (idx k) j)) = ∑ k ∈ Q, ∑ j, μ (W k j) := by
    rw [← Finset.sum_coe_sort Q (fun k => ∑ j, μ (W k j))]
    exact Equiv.sum_comp Q.equivFin.symm (fun k => ∑ j, μ (W k.1 j))
  have hclass : O (δ ^ s) * (((dyExp 1 δ + 1) ^ 2 : ℕ) : ENNReal) ≤ 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le s)]
    calc
      _ ≤ O (δ ^ s * δ ^ (-s)) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hclassBudget (Real.rpow_nonneg hδ.le s))
      _ = 1 := by rw [← Real.rpow_add hδ]; norm_num [O]
  have hretain' : O (t * δ ^ s) * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W (idx k) j) := by
    rw [hsum]
    calc
      _ = O (δ ^ s) * (O t * ∑ j, μ (Hs j)) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul ht]
        ac_rfl
      _ ≤ O (δ ^ s) * ∑ k, ∑ j, μ (W k j) := mul_le_mul' le_rfl hretain
      _ ≤ O (δ ^ s) *
          ((((dyExp 1 δ + 1) ^ 2 : ℕ) : ENNReal) * ∑ k ∈ Q, ∑ j, μ (W k j)) :=
        mul_le_mul' le_rfl hmassQ
      _ ≤ 1 * ∑ k ∈ Q, ∑ j, μ (W k j) := by
        rw [← mul_assoc]
        exact mul_le_mul' hclass le_rfl
      _ = _ := one_mul _
  let ρ' := b' / c
  have hb'e : ρ' * c = b' := div_mul_cancel₀ _ hc.ne'
  have hb' : 0 < b' := (hδ.trans_le hδa').trans_le ha'b'
  have hρ' : 0 < ρ' := div_pos hb' hc
  have hgrow' : ρ₀ ≤ ρ' := by
    obtain ⟨k, hk⟩ := hQ
    exact (le_div_iff₀ hc).mpr ((hgrow k).trans (hround k hk).2.2.1)
  have hU (k : Fin Q.card) :
      P (aRow (idx k)) (bRow (idx k)) c (z' (idx k)) (e' (idx k)) ⊆
        P a' (ρ' * c) c (z' (idx k)) (e' (idx k)) := by
    rw [hb'e]
    intro p hp
    have hr := hround (idx k) (hidx k)
    exact ⟨hp.1.trans (by linarith [hr.1]), hp.2.1.trans (by linarith [hr.2.2.1]), hp.2.2⟩
  have hdense' (k : Fin Q.card) :
      O (δ ^ h') * μ (P a' (ρ' * c) c (z' (idx k)) (e' (idx k))) ≤ μ (⋃ j, W (idx k) j) := by
    have hr := hround (idx k) (hidx k)
    have hak : 0 ≤ aRow (idx k) := hδ.le.trans (hdim (idx k)).1
    have hbk : 0 ≤ bRow (idx k) := hak.trans (hdim (idx k)).2.1
    rw [hb'e]
    calc
      _ ≤ O (δ ^ h') * ((4 : ENNReal) *
          μ (P (aRow (idx k)) (bRow (idx k)) c (z' (idx k)) (e' (idx k)))) :=
        mul_le_mul' le_rfl (prism_transverse_volume_le_four hak hbk
          (hδ.le.trans hδa') hb'.le hc.le hr.2.1 hr.2.2.2 _ _)
      _ = O (4 * δ ^ h') *
          μ (P (aRow (idx k)) (bRow (idx k)) c (z' (idx k)) (e' (idx k))) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num [O]
        ac_rfl
      _ ≤ O lam * μ (P (aRow (idx k)) (bRow (idx k)) c (z' (idx k)) (e' (idx k))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hdensityBudget) le_rfl
      _ ≤ _ := hdense (idx k)
  have hcross' (i : Fin n) (hi : i ∈ S) (k : Fin Q.card) (j : Fin L)
      (hij : f i = γ j) (hne : (Z i ∩ W (idx k) j).Nonempty) :
      Crosses δ a' (ρ' * c) c (x i) (v i) (z' (idx k)) (e' (idx k)) := by
    rw [hb'e]
    exact crosses_transverse_mono hc (hround (idx k) (hidx k)).1
      (hround (idx k) (hidx k)).2.2.1 (hcross i hi (idx k) j hij hne)
  have hbroad' (k : Fin Q.card) :
      2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100) *
        (ρ' / θ (idx k)) ^ (ω * ζ / 100) ≤ δ ^ (-h') := by
    have hθk : 0 < θ (idx k) := hθ (idx k)
    apply le_trans _ (hbroadBudget (idx k))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ hβ
    change b' / c / θ (idx k) ≤ _
    rw [div_div]
    exact div_le_div_of_nonneg_right (hround (idx k) (hidx k)).2.2.2 (by positivity)
  refine ⟨ρ', hgrow', ?_⟩
  exact incidence_prisms_of_grain_rows (fun k => W (idx k))
    (fun k => z' (idx k)) (fun k => e' (idx k)) (fun k => ν (idx k))
    (fun k => R (idx k)) (fun k => θ (idx k)) hδ hδ1 hh hδρ hρ' hβ hB hm hC₀
    (by positivity : 0 ≤ t * δ ^ s) hv hTI hC hbr hHB hδa' (by rwa [hb'e])
    (by rwa [hb'e]) (fun k => hWm (idx k)) (fun k => hWH (idx k))
    (fun j k k' hne => hWdisj j (hinj.ne hne)) (fun k j => (hWU (idx k) j).trans (hU k))
    hretain' hmassBudget hdense' hcross' (fun k => hθ (idx k))
    (fun k => hclose (idx k)) (fun k => haxis (idx k)) hbroad'

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
