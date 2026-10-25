/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SampleSheets.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleLaws
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.StableGrid
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingBand

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric MvPolynomial

noncomputable def gridConstant : ℝ := Classical.choose exists_disc_grid_lower_constant

theorem gridConstant_pos : 0 < gridConstant :=
  (Classical.choose_spec exists_disc_grid_lower_constant).1

namespace NormalizationStep.TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

theorem chosen_tests (p : s.Active) (i : Fin s.m)
    (hi : i = s.src p ∨ i = s.wit p) :
    |eval (Fin.snoc (fun j => s.sourceBase p j) (s.sourceHidden p)) (s.P i)| ≤ δ Nk L * Nk ^ a ∧
      Nk ^ (-a) ≤ |eval (Fin.snoc (fun j => s.sourceBase p j) (s.sourceHidden p))
        (pderiv (3 : Fin 4) (s.P i))| ∧
      |eval (Fin.snoc (fun j => s.sourceBase p j) (s.sourceHidden p))
        (pderiv (3 : Fin 4) (s.P i))| ≤ Nk ^ a ∧
      (cv → Nk ^ (-a) ≤ eval (fun j => s.sourceBase p j) (disc (s.P i))) := by
  have ht := ((s.hH _ _).2 _ (s.witness_mem p)).2.2.2.2.2
  apply ht.1 (s.P i)
  rcases hi with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem grid_discriminants_pos (hcv : cv) (hNk : 0 < Nk)
    {mesh r : ℝ} (hmesh : 0 < mesh) (hmr : mesh ≤ r) (hr16 : r ≤ 1 / 16)
    (hsmall : 9 * gridConstant * Nk ^ a * r < Nk ^ (-a)) (p : s.Active) :
    DiscPosOn (s.P (s.src p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r ∧
      DiscPosOn (s.P (s.wit p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r := by
  have hp (i : Fin s.m) (hi : i = s.src p ∨ i = s.wit p) :
      DiscPosOn (s.P i) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r := by
    have hP := (s.hP i).2.2 hcv
    have hlower := (Classical.choose_spec exists_disc_grid_lower_constant).2 (s.P i) hP.2.1
      (Nk ^ a) (Nk ^ (-a)) r (Real.rpow_nonneg hNk.le _)
      (Real.rpow_pos_of_pos hNk _) (hmesh.trans_le hmr) hr16 hP.2.2
      (s.sourceBase p) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) (s.sourceBase_norm p)
      ((norm_sub_gridCenter_le hmesh _).trans hmr)
      ((s.chosen_tests p i hi).2.2.2 hcv)
    intro ζ hζ
    have hh := hlower ζ hζ
    change Nk ^ (-a) - 9 * gridConstant * Nk ^ a * r ≤ _ at hh
    linarith
  exact ⟨hp _ (Or.inl rfl), hp _ (Or.inr rfl)⟩

/-- The common nearest-root error for both colours of the tested law. -/
noncomputable def sheetError
    (_s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε) : ℝ :=
  2 * (δ Nk L * Nk ^ a) / Nk ^ (-a)

theorem sheetError_pos (hNk : 0 < Nk) : 0 < s.sheetError := by
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  dsimp [sheetError]
  exact div_pos (mul_pos (by norm_num) (mul_pos hδ (Real.rpow_pos_of_pos hNk _)))
    (Real.rpow_pos_of_pos hNk _)

theorem sheetError_eq (hNk : 0 < Nk) : s.sheetError = 2 * δ Nk L * (Nk ^ a) ^ 2 := by
  dsimp [sheetError]
  rw [Real.rpow_neg hNk.le, div_inv_eq_mul]
  ring

theorem nearest_root_error (hNk : 0 < Nk) (p : s.Active) (i : Fin s.m)
    (hi : i = s.src p ∨ i = s.wit p) :
    2 * |eval (Fin.snoc (fun j => s.sourceBase p j) (s.sourceHidden p)) (s.P i)| /
      |eval (Fin.snoc (fun j => s.sourceBase p j) (s.sourceHidden p))
        (pderiv (3 : Fin 4) (s.P i))| ≤ s.sheetError := by
  have ht := s.chosen_tests p i hi
  have hδ : 0 ≤ δ Nk L := by unfold δ; positivity
  exact div_le_div₀ (mul_nonneg (by norm_num) (mul_nonneg hδ (Real.rpow_nonneg hNk.le _)))
    (mul_le_mul_of_nonneg_left ht.1 (by norm_num)) (Real.rpow_pos_of_pos hNk _) ht.2.1

/-- Convert the exact normalized tested record into the generic sheet-matching law. -/
noncomputable def toPairTests (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 0 < Nk)
    {mesh r : ℝ} (hmesh : 0 < mesh) (hmr : mesh ≤ r)
    (hpos : ∀ p : s.Active,
      DiscPosOn (s.P (s.src p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r ∧
      DiscPosOn (s.P (s.wit p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r) :
    PairTests (Fin s.m) (Fin s.J) s.Active where
  Pm := s.pairMeasure
  frameOf := s.frame
  P := s.P
  src := s.src
  wit := s.wit
  z := s.sourceBase
  w := s.sourceHidden
  h := mesh
  r := r
  Δ := s.sheetError
  ρn := s.sourceCeiling
  finite := s.pairMeasure_finite
  deg := fun i => (s.hP i).1
  src_meas := s.measurableSet_src_eq
  wit_meas := s.measurableSet_wit_eq
  z_meas := s.measurable_sourceBase
  w_meas := s.measurable_sourceHidden
  frame_eq := s.frame_src_wit
  z_mem := s.sourceBase_norm
  h_pos := hmesh
  h_le := hmr
  pos_src := fun p => (hpos p).1
  pos_wit := fun p => (hpos p).2
  ne_src := fun p => by
    have hfloor := (s.chosen_tests p _ (Or.inl rfl)).2.1
    have hpos := Real.rpow_pos_of_pos hNk (-a)
    intro hzero
    rw [hzero, abs_zero] at hfloor
    linarith
  ne_wit := fun p => by
    have hfloor := (s.chosen_tests p _ (Or.inr rfl)).2.1
    have hpos := Real.rpow_pos_of_pos hNk (-a)
    intro hzero
    rw [hzero, abs_zero] at hfloor
    linarith
  near_src := fun p => s.nearest_root_error hNk p _ (Or.inl rfl)
  near_wit := fun p => s.nearest_root_error hNk p _ (Or.inr rfl)
  Δ_pos := s.sheetError_pos hNk
  ρn_nonneg := s.sourceCeiling_nonneg hω hNk.le
  dens_src := s.source_density hω
  dens_wit := s.witness_density hω

end NormalizationStep.TestedSample

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
