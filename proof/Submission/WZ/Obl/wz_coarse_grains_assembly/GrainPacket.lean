-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.GrainPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Split
import Submission.WZ.Obl.wz_coarse_grains_assembly.ExactMultiplicity
import Submission.WZ.Obl.wz_coarse_grains_assembly.ColorRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- The geometric output for the grains of one coarse tube. Multiplicity
and broadness are recorded separately so they can be regularized. -/
structure GrainPacket (δ h ρ c : ℝ) {n : ℕ} (x v : Fin n → V)
    (Z : Fin n → Set V) (y w : V) where
  L : ℕ
  center : Fin L → V
  frame : Fin L → V ≃ₗᵢ[ℝ] V
  shading : Fin L → Set V
  geometry : ∀ j, MeasurableSet (shading j) ∧
    shading j ⊆ P (16 * δ) (ρ * c) c (center j) (frame j) ∧
    P (16 * δ) (ρ * c) c (center j) (frame j) ⊆ T ρ y w ∧
    ι (frame j w) 0 ^ 2 + ι (frame j w) 1 ^ 2 ≤ (10 * ρ) ^ 2
  disjoint : ∀ j j', j ≠ j' → Disjoint (shading j) (shading j')
  cover : {p | ∃ j, p ∈ shading j} = {p | ∃ i, p ∈ Z i}
  density : O (δ ^ h * L * (16 * δ) * (ρ * c) * c) ≤ ∑ j, μ (shading j)
  crossing : ∀ i j, (Z i ∩ shading j).Nonempty →
    Z i ∩ P (16 * δ) (ρ * c) c (center j) (frame j) ⊆ shading j ∧
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P (16 * δ) (ρ * c) c (center j) (frame j)),
      |ι (frame j (p - center j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ (x i) (v i) ∩ P (16 * δ) (ρ * c) c (center j) (frame j),
        ι (frame j (p - center j)) 2 = t

/-- A refinement preserving the whole union preserves every grain and its
density and crossing properties. -/
def GrainPacket.refine {δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Z W : Fin n → Set V} {y w : V} (D : GrainPacket δ h ρ c x v Z y w)
    (hWZ : ∀ i, W i ⊆ Z i)
    (hunion : {p | ∃ i, p ∈ W i} = {p | ∃ i, p ∈ Z i}) :
    GrainPacket δ h ρ c x v W y w where
  L := D.L
  center := D.center
  frame := D.frame
  shading := D.shading
  geometry := D.geometry
  disjoint := D.disjoint
  cover := D.cover.trans hunion.symm
  density := D.density
  crossing := by
    intro i j hne
    have hold := D.crossing i j (hne.mono (Set.inter_subset_inter_left _ (hWZ i)))
    exact ⟨(Set.inter_subset_inter_left _ (hWZ i)).trans hold.1, hold.2⟩

/-- Increasing the error parameter only weakens the density clause. -/
def GrainPacket.mono_error {δ h h' ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Z : Fin n → Set V} {y w : V} (D : GrainPacket δ h ρ c x v Z y w)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (hρ : 0 ≤ ρ) (hc : 0 ≤ c) :
    GrainPacket δ h' ρ c x v Z y w where
  L := D.L
  center := D.center
  frame := D.frame
  shading := D.shading
  geometry := D.geometry
  disjoint := D.disjoint
  cover := D.cover
  density := by
    apply le_trans (ENNReal.ofReal_le_ofReal _) D.density
    have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hh
    gcongr
  crossing := D.crossing

/-- Exact multiplicity can be imposed without discarding any grain
shading. The same factor controls the mass and angular-count losses. -/
theorem GrainPacket.exact_multiplicity {δ h ρ c C β : ℝ} {n M : ℕ}
    {x v : Fin n → V} {Z : Fin n → Set V} {y w : V}
    (D : GrainPacket δ h ρ c x v Z y w)
    (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hM : 0 < M) (hC : 0 ≤ C)
    (hZ : ∀ i, MeasurableSet (Z i))
    (hmult : ∀ p, (∃ i, p ∈ Z i) →
      (M : ℝ) ≤ q n {i | p ∈ Z i} ∧ q n {i | p ∈ Z i} ≤ C * M)
    (hbr : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ β * q n {i | p ∈ Z i}) :
    ∃ W : Fin n → Set V,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      Nonempty (GrainPacket δ h ρ c x v W y w) ∧
      (∑ i, μ (Z i)) ≤ O C * ∑ i, μ (W i) ∧
      (∀ p, (∃ i, p ∈ W i) → q n {i | p ∈ W i} = M) ∧
      ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
        q n {i | p ∈ W i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
          (C * δ ^ (-h)) * (r / ρ) ^ β * q n {i | p ∈ W i} := by
  obtain ⟨W, hW, hunion, hexact, hfrac, hmass⟩ :=
    exact_multiplicity_with_mass hM hC Z hZ hmult
  refine ⟨W, hW, ⟨D.refine (fun i => (hW i).2) hunion⟩, hmass, hexact, ?_⟩
  exact broad_of_pointwise_fraction hδ hρ (Real.rpow_nonneg hδ _)
    (fun i => (hW i).2) (fun p _ => hfrac p) hbr

end WangZahlLot.Obl.wz_coarse_grains_assembly
