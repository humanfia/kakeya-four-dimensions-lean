-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.FiniteVelocityCodes

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open MeasureTheory Set Finset

/-- Exact vector velocity codes. This extends the scalar code construction
(adapted in FiniteVelocityCodes from o107/x0735) to the ORIGINAL two velocity
coordinates, before choosing a parent's major axis. The large history
alphabet does not enter the palette count. -/
theorem exists_history_vector_velocity_code
    {Y H : Type*} [MeasurableSpace Y] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Fintype H] (d : ℕ)
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (history : Y → H) (hhistory : Measurable history)
    (velocity : Y → Fin d → ℝ) (hvelocity : Measurable velocity)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hbound : ∀ᵐ y ∂μ, ∀ e, |velocity y e| ≤ R) :
    ∃ n : ℕ, 0 < n ∧ ∃ (code : Y → Fin n) (decode : Fin n → H)
      (palette : Fin n → (Fin d → {j : ℤ // j ∈ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋})),
      Measurable code ∧
      (∀ᵐ y ∂μ, decode (code y) = history y ∧
        ∀ e, (palette (code y) e : ℤ) = ⌊velocity y e / δ⌋) ∧
      (∀ i, ∃ y, (∀ e, |velocity y e| ≤ R) ∧ decode i = history y ∧
        ∀ e, (palette i e : ℤ) = ⌊velocity y e / δ⌋) ∧
      ∀ S : Finset (Fin n), (S.image palette).card ≤
        (Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋).card ^ d := by
  classical
  let V : Finset ℤ := Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋
  have hzero : (0 : ℤ) ∈ V := by
    apply Finset.mem_Icc.mpr
    constructor
    · simpa using Int.floor_mono (show -R / δ ≤ (0 : ℝ) by
        rw [neg_div]
        exact neg_nonpos.mpr (div_nonneg hR hδ.le))
    · exact Int.floor_nonneg.mpr (by positivity)
  let Z := Fin d → {j : ℤ // j ∈ V}
  let clamp : ℤ → {j : ℤ // j ∈ V} :=
    fun j => if hj : j ∈ V then ⟨j, hj⟩ else ⟨0, hzero⟩
  let pal : Y → Z := fun y e => clamp ⌊velocity y e / δ⌋
  have hpal : Measurable pal := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_of_countable clamp).comp
      (((measurable_pi_apply e).comp hvelocity).div_const δ).floor
  let U : Set Y := {y | ∀ e, |velocity y e| ≤ R}
  have hU : MeasurableSet U := by
    simp only [U, setOf_forall]
    apply MeasurableSet.iInter
    intro e
    exact measurableSet_le ((measurable_pi_apply e).comp hvelocity).abs measurable_const
  have hfull : μ Uᶜ = 0 := ae_iff.mp hbound
  have hallowed (y : Y) (hy : y ∈ U) (e : Fin d) : ⌊velocity y e / δ⌋ ∈ V :=
    Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hy e)).1 hδ.le),
        Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hy e)).2 hδ.le)⟩
  have hpal_eq (y : Y) (hy : y ∈ U) (e : Fin d) :
      (pal y e : ℤ) = ⌊velocity y e / δ⌋ := by
    dsimp [pal, clamp]
    rw [dite_eq_left (hallowed y hy e)]
  have hG : Measurable (fun y => (history y, pal y)) := hhistory.prodMk hpal
  obtain ⟨n, hn, code, decode, hcode, hdecode, hrep⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_ae
      μ U hU hfull (fun y => (history y, pal y)) hG (Set.toFinite _)
  refine ⟨n, hn, code, (fun i => (decode i).1), (fun i => (decode i).2), hcode, ?_, ?_, ?_⟩
  · filter_upwards [hbound] with y hy
    have h := hdecode y hy
    refine ⟨congrArg Prod.fst h, fun e => ?_⟩
    exact (congrArg (fun p => (p.2 e : ℤ)) h).trans (hpal_eq y hy e)
  · intro i
    obtain ⟨y, hy, heq⟩ := hrep i
    have h := heq.symm
    refine ⟨y, hy, congrArg Prod.fst h, fun e => ?_⟩
    exact (congrArg (fun p => (p.2 e : ℤ)) h).trans (hpal_eq y hy e)
  · intro S
    have hc : Fintype.card Z = V.card ^ d := by simp only [Z, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    exact (Finset.card_le_univ _).trans_eq hc

end

end Submission.Obl.k4_finite_affine_parent_sources
