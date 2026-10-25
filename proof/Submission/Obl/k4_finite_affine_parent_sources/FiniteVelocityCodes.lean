-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/FiniteVelocityCodes.lean.
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode
import Submission.Lib.K4AngularCharge.ChartCells

/-! Exact finite codes for a measurable bounded velocity and arbitrary
finite histories. The velocity alphabet has the mesh-size bound needed
for the entropy window; the joint source code can be much larger. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open MeasureTheory Set Finset

/-- The number of possible velocity bins depends on the velocity range
and its requested fine mesh, independently of all other source records. -/
theorem velocity_bin_count {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ((Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card : ℝ) ≤ 2 * R / δ + 2 := by
  have h := Submission.Lib.K4AngularCharge.card_Icc_floor_le (-R / δ) (R / δ)
    (div_le_div_of_nonneg_right (by linarith) hδ.le)
  convert h using 1 <;> ring

/-- A finite joint code stores every original history and the actual fine
velocity bin on a full-mass measurable support. Every decoded code has an
actual original representative. The palette alphabet retains its own small
cardinality, even when the history alphabet is much larger. -/
theorem exists_history_velocity_code
    {Y H : Type*} [MeasurableSpace Y] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Fintype H]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (history : Y → H) (hhistory : Measurable history)
    (velocity : Y → ℝ) (hvelocity : Measurable velocity)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R) (hbound : ∀ᵐ y ∂μ, |velocity y| ≤ R) :
    ∃ n : ℕ, 0 < n ∧ ∃ (code : Y → Fin n) (decode : Fin n → H)
      (palette : Fin n → {j : ℤ // j ∈ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋}),
      Measurable code ∧
      (∀ᵐ y ∂μ, decode (code y) = history y ∧ (palette (code y) : ℤ) = ⌊velocity y / δ⌋) ∧
      (∀ i, ∃ y, |velocity y| ≤ R ∧ decode i = history y ∧ (palette i : ℤ) = ⌊velocity y / δ⌋) ∧
      ∀ S : Finset (Fin n), (S.image palette).card ≤
        (Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card := by
  classical
  let V : Finset ℤ := Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋
  have hzero : (0 : ℤ) ∈ V := by
    apply Finset.mem_Icc.mpr
    constructor
    · simpa using Int.floor_mono (show -R / δ ≤ (0 : ℝ) by
        rw [neg_div]
        exact neg_nonpos.mpr (div_nonneg hR hδ.le))
    · exact Int.floor_nonneg.mpr (by positivity)
  let Z := {j : ℤ // j ∈ V}
  let clamp : ℤ → Z := fun j => if hj : j ∈ V then ⟨j, hj⟩ else ⟨0, hzero⟩
  let pal : Y → Z := fun y => clamp ⌊velocity y / δ⌋
  have hpal : Measurable pal := (measurable_of_countable clamp).comp (hvelocity.div_const δ).floor
  let U : Set Y := {y | |velocity y| ≤ R}
  have hU : MeasurableSet U := measurableSet_le hvelocity.abs measurable_const
  have hfull : μ Uᶜ = 0 := ae_iff.mp hbound
  have hallowed (y : Y) (hy : y ∈ U) : ⌊velocity y / δ⌋ ∈ V :=
    Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hy).1 hδ.le),
        Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hy).2 hδ.le)⟩
  have hpal_eq (y : Y) (hy : y ∈ U) : (pal y : ℤ) = ⌊velocity y / δ⌋ := by
    dsimp [pal, clamp]
    rw [dite_eq_left (hallowed y hy)]
  have hG : Measurable (fun y => (history y, pal y)) := hhistory.prodMk hpal
  obtain ⟨n, hn, code, decode, hcode, hdecode, hrep⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_ae
      μ U hU hfull (fun y => (history y, pal y)) hG (Set.toFinite _)
  refine ⟨n, hn, code, (fun i => (decode i).1), (fun i => (decode i).2), hcode, ?_, ?_, ?_⟩
  · filter_upwards [hbound] with y hy
    have h := hdecode y hy
    exact ⟨congrArg Prod.fst h, (congrArg (fun p => (p.2 : ℤ)) h).trans (hpal_eq y hy)⟩
  · intro i
    obtain ⟨y, hy, heq⟩ := hrep i
    have h := heq.symm
    exact ⟨y, hy, congrArg Prod.fst h, (congrArg (fun p => (p.2 : ℤ)) h).trans (hpal_eq y hy)⟩
  · intro S
    have hc : Fintype.card Z = V.card := Fintype.card_coe V
    exact (Finset.card_le_univ _).trans_eq hc

end

end Submission.Obl.k4_finite_affine_parent_sources
