-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 37b81a6e.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ParentChoice.lean.
-- Uses this obligation's checked nuE interface for the original conditional prior.
import Submission.Obl.k4_finite_affine_parent_sources.MarginalFloors
import Submission.Obl.k4_finite_affine_parent_sources.ParentLikelihoodPreparation
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-! Choose one original parent after a substantial sparse restriction. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open MeasureTheory Set Finset Classical

/-- The full old prior weights multiplied by their original block duration
have total at most one. This is the accepted assignment budget in the
real units used for choosing a prepared parent. -/
theorem weighted_full_prior_block_budget
    {X ι Γ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype Γ] (T : ℕ)
    (ν : Γ → Measure X) [∀ γ, IsProbabilityMeasure (ν γ)]
    (ω : Γ → ℝ) (hω : ∀ γ, 0 ≤ ω γ) (hω1 : ∑ γ, ω γ = 1)
    (world : ι → Γ) (block : ι → Fin (2 ^ T)) (A : ι → Set X)
    (hA : ∀ b, MeasurableSet (A b))
    (hdisj : ∀ b b', b ≠ b' → world b = world b' → block b = block b' →
      Disjoint (A b) (A b')) :
    (∑ b, ω (world b) * (1 / (2 : ℝ) ^ T) * (ν (world b)).real (A b)) ≤ 1 := by
  have hh := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    ν ω world block A (fun γ => inferInstance) hω hω1 hA hdisj
  have hr := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hh
  rw [ENNReal.toReal_sum (fun b _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (ν (world b)) (A b)))] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω _),
    ENNReal.toReal_natCast, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hr
  calc
    _ = (∑ b, ω (world b) * (ν (world b)).real (A b)) / (2 : ℝ) ^ T := by
      rw [sum_div]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ T)).mpr hr

/-- One positive parent has both a current/reference success floor and a
current/full-prior reference floor. All weights are the original weights. -/
theorem exists_parent_two_reference_floors
    {H : Type*} [Fintype H] [DecidableEq H]
    (P R w : H → ℝ) (hP : ∀ a, 0 ≤ P a) (_hR : ∀ a, 0 ≤ R a)
    (hw : ∀ a, 0 ≤ w a) (hRP : ∀ a, R a ≤ P a)
    (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hP1 : ∑ a, P a ≤ 1) (hwB : ∑ a, w a ≤ B) (hcurrent : δ ≤ ∑ a, R a) :
    ∃ a, 0 < R a ∧ 0 < P a ∧ δ / 4 * P a ≤ R a ∧ δ / (4 * B) * w a ≤ R a := by
  let cells : H ⊕ H → Finset H := Sum.elim (fun a => {a}) (fun a => {a})
  let threshold : H ⊕ H → ℝ :=
    Sum.elim (fun a => δ / 4 * P a) (fun a => δ / (4 * B) * w a)
  have hthreshold : ∀ a, 0 ≤ threshold a := by
    intro a
    cases a with
    | inl a => exact mul_nonneg (by positivity) (hP a)
    | inr a => exact mul_nonneg (by positivity) (hw a)
  have htotal : (∑ a, threshold a) ≤ δ / 2 := by
    calc
      _ = δ / 4 * (∑ a, P a) + δ / (4 * B) * (∑ a, w a) := by
        rw [Fintype.sum_sum_type]
        dsimp only [threshold, Sum.elim_inl, Sum.elim_inr]
        rw [← mul_sum, ← mul_sum]
      _ ≤ δ / 4 * 1 + δ / (4 * B) * B := add_le_add
        (mul_le_mul_of_nonneg_left hP1 (by positivity))
        (mul_le_mul_of_nonneg_left hwB (by positivity))
      _ = δ / 2 := by field_simp; ring
  obtain ⟨S, _, hmass, hfloor⟩ := exists_simultaneous_marginal_floors
    univ R cells threshold hthreshold
  have hmasspos : 0 < ∑ a ∈ S, R a := by
    linarith only [hmass, htotal, hcurrent, hδ]
  have hex : ∃ a ∈ S, 0 < R a := by
    by_contra hn
    push Not at hn
    have hh : (∑ a ∈ S, R a) ≤ 0 := sum_nonpos fun a ha => hn a ha
    exact (not_le_of_gt hmasspos) hh
  obtain ⟨a, ha, hRa⟩ := hex
  have hactive : (S ∩ ({a} : Finset H)).Nonempty := by simp [ha]
  have hfirst := hfloor (Sum.inl a) hactive
  have hsecond := hfloor (Sum.inr a) hactive
  refine ⟨a, hRa, hRa.trans_le (hRP a), ?_, ?_⟩
  · simpa only [cells, threshold, Sum.elim_inl, Finset.inter_singleton_of_mem ha, sum_singleton] using hfirst
  · simpa only [cells, threshold, Sum.elim_inr, Finset.inter_singleton_of_mem ha, sum_singleton] using hsecond

/-- A finite measurable original-parent record supplies the same choice
for the continuous original law. The current parent submeasure is scaled
by the ORIGINAL parent mass and keeps an inverse-subpower success floor. -/
theorem exists_original_parent_reference_floors
    {Y : Type} {H : Type*} [MeasurableSpace Y] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Fintype H] [DecidableEq H]
    (reference current : Measure Y) [IsFiniteMeasure reference]
    (hcurrent : current ≤ reference) (parent : Y → H) (hparent : Measurable parent)
    (w : H → ℝ) (hw : ∀ a, 0 ≤ w a) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hreference : reference.real Set.univ ≤ 1)
    (hwB : ∑ a, w a ≤ B) (hmass : δ ≤ current.real Set.univ) :
    ∃ a, reference {y | parent y = a} ≠ 0 ∧
      δ / (4 * B) * w a ≤ current.real {y | parent y = a} ∧
      IsProbabilityMeasure (nuE reference {y | parent y = a}) ∧
      δ / 4 ≤ (fixedParentRestriction reference current {y | parent y = a}).real Set.univ := by
  have : IsFiniteMeasure current := isFiniteMeasure_of_le reference hcurrent
  let P := fun a => reference.real (parent ⁻¹' {a})
  let R := fun a => current.real (parent ⁻¹' {a})
  have hsum (μ : Measure Y) [IsFiniteMeasure μ] :
      (∑ a : H, μ.real (parent ⁻¹' {a})) = μ.real Set.univ := by
    simpa using sum_measureReal_preimage_singleton (μ := μ) univ
      (fun a _ => hparent (measurableSet_singleton a))
  have hRP (a : H) : R a ≤ P a :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hcurrent _)
  obtain ⟨a, hRa, hPa, hsuccess, hprior⟩ := exists_parent_two_reference_floors
    P R w (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hw hRP
    B δ hB hδ (by simpa only [P, hsum] using hreference) hwB
      (by simpa only [R, hsum] using hmass)
  have ha : reference {y | parent y = a} ≠ 0 := by
    intro hz
    change reference (parent ⁻¹' {a}) = 0 at hz
    have hzero : P a = 0 := by simp only [P, measureReal_def, hz, ENNReal.toReal_zero]
    exact hPa.ne' hzero
  refine ⟨a, ha, hprior, nuE_isProb reference _ ha (measure_ne_top _ _), ?_⟩
  rw [fixedParentRestriction_real _ _ _ _ MeasurableSet.univ, Set.univ_inter]
  exact (le_div_iff₀ hPa).mpr hsuccess

end

end Submission.Obl.k4_finite_affine_parent_sources
