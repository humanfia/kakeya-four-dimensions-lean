import Submission.Obl.k4_scalar_normalized_exact_refinement.WorldSelection
import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass
import Submission.Obl.k4_scalar_crop_profile_transport.Geometry

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set Filter
open k4_scalar_linear_critical_extremizers.Split
open scoped ENNReal

noncomputable section

namespace WorldSelection

def positiveCount {ι : Type*} [Fintype ι] (mass : ι → ENNReal) : ℕ :=
  Fintype.card {i // 0 < mass i}

def positiveEmbedding {ι : Type*} [Fintype ι] (mass : ι → ENNReal) :
    Fin (positiveCount mass) ↪ ι :=
  ⟨fun i => ((Fintype.equivFin {i // 0 < mass i}).symm i).1,
    fun _ _ he => (Fintype.equivFin {i // 0 < mass i}).symm.injective (Subtype.ext he)⟩

lemma positiveEmbedding_pos {ι : Type*} [Fintype ι] (mass : ι → ENNReal)
    (i : Fin (positiveCount mass)) : 0 < mass (positiveEmbedding mass i) :=
  ((Fintype.equivFin {i // 0 < mass i}).symm i).2

lemma mass_zero_off_positive {ι : Type*} [Fintype ι] (mass : ι → ENNReal)
    (i : ι) (hi : i ∉ range (positiveEmbedding mass)) : mass i = 0 := by
  by_contra hz
  have hp : 0 < mass i := pos_iff_ne_zero.mpr hz
  have he : positiveEmbedding mass ((Fintype.equivFin {i // 0 < mass i}) ⟨i, hp⟩) = i :=
    congrArg Subtype.val ((Fintype.equivFin {i // 0 < mass i}).symm_apply_apply ⟨i, hp⟩)
  exact hi ⟨_, he⟩

lemma positive_weight_budget {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (mass : ι → ENNReal) (K : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hK : 0 < K)
    (hmass1 : ∀ i, mass i ≤ 1)
    (hmass : ENNReal.ofReal K⁻¹ ≤ ∑ i, ENNReal.ofReal (w i) * mass i) :
    K⁻¹ ≤ (∑ i, w (positiveEmbedding mass i)) ∧
      (∑ i, w (positiveEmbedding mass i)) ≤ 1 := by
  classical
  let e := positiveEmbedding mass
  have hZ0 : 0 ≤ ∑ i, w (e i) := Finset.sum_nonneg (fun _ _ => hw _)
  have hZeq : ENNReal.ofReal (∑ i, w (e i)) = ∑ i, ENNReal.ofReal (w (e i)) :=
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => hw _)
  have hmassEq : (∑ i, ENNReal.ofReal (w (e i)) * mass (e i)) =
      ∑ i, ENNReal.ofReal (w i) * mass i := by
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      rw [mass_zero_off_positive mass i hi, mul_zero]
    · intro i
      rfl
  constructor
  · have he : ENNReal.ofReal K⁻¹ ≤ ENNReal.ofReal (∑ i, w (e i)) := by
      rw [hZeq]
      apply hmass.trans
      rw [← hmassEq]
      exact Finset.sum_le_sum (fun i _ => by simpa using mul_le_mul' le_rfl (hmass1 (e i)))
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    simpa only [ENNReal.toReal_ofReal (inv_pos.mpr hK).le, ENNReal.toReal_ofReal hZ0] using hh
  · calc
      ∑ i, w (e i) = ∑ i ∈ Finset.univ.map e, w i := (Finset.sum_map _ e w).symm
      _ ≤ ∑ i, w i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hw i)
      _ = 1 := hsum

variable (p : Code)

def positiveWorldCount (k : ℕ) : ℕ := positiveCount (fun i => mu p k i univ)
def positiveWorldEmbedding (k : ℕ) : Fin (positiveWorldCount p k) ↪ Fin (W p k) :=
  positiveEmbedding (fun i => mu p k i univ)
def positiveWorldBudget (k : ℕ) : ℝ := ∑ i, ω p k (positiveWorldEmbedding p k i)
def positiveWorldMultiplier (k : ℕ) : ℝ := (positiveWorldBudget p k)⁻¹

lemma positiveWorldBudget_bounds (hp : Spec.RawScalar p) (k : ℕ) :
    (K p k)⁻¹ ≤ positiveWorldBudget p k ∧ positiveWorldBudget p k ≤ 1 := by
  have hw := hp.2 k
  apply positive_weight_budget (ω p k) (fun i => mu p k i univ) (K p k)
    hw.2.1 hw.2.2.1
  · have hK : 1 ≤ K p k := hp.1.2.2.1.1 k
    linarith
  · intro i
    let : IsProbabilityMeasure (ν p k i) := (hw.2.2.2.1 i).1
    exact k4_scalar_crop_profile_transport.selected_mass_le_one _ _ (hw.2.2.2.1 i).2.2.2.2.1
  · exact hw.2.2.2.2

lemma positiveWorldBudget_pos (hp : Spec.RawScalar p) (k : ℕ) : 0 < positiveWorldBudget p k := by
  have hK : 1 ≤ K p k := hp.1.2.2.1.1 k
  exact (inv_pos.mpr (by linarith)).trans_le (positiveWorldBudget_bounds p hp k).1

lemma positiveWorldMultiplier_bounds (hp : Spec.RawScalar p) (k : ℕ) :
    1 ≤ positiveWorldMultiplier p k ∧ positiveWorldMultiplier p k ≤ K p k := by
  have hZ := positiveWorldBudget_bounds p hp k
  have hZ0 := positiveWorldBudget_pos p hp k
  have hK : 1 ≤ K p k := hp.1.2.2.1.1 k
  exact ⟨by simpa [positiveWorldMultiplier] using inv_anti₀ hZ0 hZ.2,
    by simpa [positiveWorldMultiplier] using inv_anti₀ (inv_pos.mpr (by linarith)) hZ.1⟩

def positiveCode : Code := code p (positiveWorldCount p) (positiveWorldEmbedding p) (positiveWorldMultiplier p)

lemma positive_weights_sum (hp : Spec.RawScalar p) (k : ℕ) :
    (∑ i, positiveWorldMultiplier p k * ω p k (positiveWorldEmbedding p k i)) = 1 := by
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ (positiveWorldBudget_pos p hp k).ne'

lemma positive_success (hp : Spec.RawScalar p) (k : ℕ) :
    ENNReal.ofReal ((K p k)⁻¹) ≤
      ∑ i, ENNReal.ofReal (positiveWorldMultiplier p k * ω p k (positiveWorldEmbedding p k i)) *
        mu p k (positiveWorldEmbedding p k i) univ := by
  have hce : 1 ≤ ENNReal.ofReal (positiveWorldMultiplier p k) := by
    simpa using ENNReal.ofReal_le_ofReal (positiveWorldMultiplier_bounds p hp k).1
  have hsum : (∑ i, ENNReal.ofReal (ω p k (positiveWorldEmbedding p k i)) *
      mu p k (positiveWorldEmbedding p k i) univ) =
      ∑ j, ENNReal.ofReal (ω p k j) * mu p k j univ := by
    apply Fintype.sum_of_injective (positiveWorldEmbedding p k) (positiveWorldEmbedding p k).injective
    · intro i hi
      rw [mass_zero_off_positive (fun i => mu p k i univ) i hi, mul_zero]
    · intro i
      rfl
  simp_rw [ENNReal.ofReal_mul (by linarith [(positiveWorldMultiplier_bounds p hp k).1]), mul_assoc]
  rw [← Finset.mul_sum, hsum]
  have hsource : ENNReal.ofReal ((K p k)⁻¹) ≤
      ∑ j, ENNReal.ofReal (ω p k j) * mu p k j univ := (hp.2 k).2.2.2.2
  apply hsource.trans
  calc
    _ = 1 * ∑ j, ENNReal.ofReal (ω p k j) * mu p k j univ := by simp
    _ ≤ _ := mul_le_mul' hce le_rfl

theorem positive_raw (hp : Spec.RawScalar p) : Spec.RawScalar (positiveCode p) := by
  apply raw p (positiveWorldCount p) (positiveWorldEmbedding p) (positiveWorldMultiplier p) hp
  · intro k
    linarith [(positiveWorldMultiplier_bounds p hp k).1]
  · exact positive_weights_sum p hp
  · exact positive_success p hp

theorem positive_pure (hp : Spec.RawScalar p) (hpure : Spec.PureProfile p) :
    Spec.PureProfile (positiveCode p) := by
  apply pure p (positiveWorldCount p) (positiveWorldEmbedding p) (positiveWorldMultiplier p) hp hpure
  · intro k
    linarith [(positiveWorldMultiplier_bounds p hp k).1]
  · intro η hη
    filter_upwards [hp.1.2.2.1.2 η hη] with k hk
    exact (positiveWorldMultiplier_bounds p hp k).2.trans hk

lemma positive_selected_pos (k : ℕ) (i : Fin (W (positiveCode p) k)) :
    0 < mu (positiveCode p) k i univ := by
  change Fin (positiveCount (fun j => mu p k j univ)) at i
  change 0 < mu p k (positiveEmbedding (fun j => mu p k j univ) i) univ
  exact positiveEmbedding_pos (fun j => mu p k j univ) i

end WorldSelection

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
