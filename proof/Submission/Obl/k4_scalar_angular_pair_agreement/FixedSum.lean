import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.Fixed

/-!
# Summing the fixed-scale estimates

The exceptional parts of the bad witnesses sum to at most the weighted cap exceptional
mass; the non-exceptional parts, through the true floors, to an explicit power of `N`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

section Sums

open scoped Classical

lemma ofReal_two_pow (T : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ T) = ((2 ^ T : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_natCast]; push_cast; rfl

lemma ofReal_two_pow_mul_inv {T₁ T : ℕ} (hT₁ : T₁ ≤ T) :
    ENNReal.ofReal ((2 : ℝ) ^ T₁) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
      ENNReal.ofReal ((2 : ℝ) ^ (T - T₁)) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    two_pow_split hT₁]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ T₁ := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (T - T₁) := by positivity
  rw [show (2 : ℝ) ^ T₁ * ((2 : ℝ) ^ T₁ * (2 : ℝ) ^ (T - T₁))⁻¹ * (2 : ℝ) ^ (T - T₁) = 1 by
    field_simp]
  exact ENNReal.ofReal_one

/-- The selected incidences of one world have total measure at most one. -/
lemma sum_mu_C_le_one {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) (w : Fin (W p k))
    [IsProbabilityMeasure (ν p k w)] :
    ∑ i ∈ Finset.univ.filter (fun i => γ i = w), mu p k w (C i) ≤ 1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i => γ i = w))
    (t := Finset.univ) (g := j) (fun i _ => Finset.mem_univ _)]
  calc ∑ j' : Fin (2 ^ T), ∑ i ∈ Finset.univ.filter (fun i => γ i = w) with j i = j',
        mu p k w (C i)
      ≤ ∑ _j' : Fin (2 ^ T), ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
        apply Finset.sum_le_sum
        intro j' _
        rw [← measure_biUnion_finset]
        · refine (Measure.restrict_le_self _).trans ?_
          calc ((ν p k w).prod volume) _ ≤ ((ν p k w).prod volume) (univ ×ˢ I T j') := by
                apply measure_mono
                intro q hq
                simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hq
                obtain ⟨i, ⟨_, hij⟩, hq⟩ := hq
                have := ((hCsub i hq).2).2
                rw [hij] at this
                exact ⟨trivial, this⟩
            _ = ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
                rw [Measure.prod_prod, measure_univ, one_mul, volume_I]
        · intro i hi i' hi' hne
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_ofPred_eq] at hi hi'
          have hA := hdisj i i' hne (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm)
          refine Disjoint.mono (fun q hq => ((hCsub i hq).2).1) (fun q hq => ((hCsub i' hq).2).1) ?_
          exact Set.disjoint_left.mpr (fun q h1 h2 => Set.disjoint_left.mp hA h1 h2)
        · intro i _; exact hC i
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ofReal_two_pow, ← ENNReal.ofReal_mul (by positivity)]
        rw [show (2 : ℝ) ^ T * ((2 : ℝ) ^ T)⁻¹ = 1 by field_simp]
        exact ENNReal.ofReal_one

/-- The exceptional parts of the bad witnesses of one world add up to at most its cap
exceptional mass. -/
lemma exc_sum_le {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hA : ∀ i, MeasurableSet (A i))
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) {T₁ : ℕ} (hT₁ : T₁ ≤ T) (uu τ : ℝ)
    (w : Fin (W p k)) [IsProbabilityMeasure (ν p k w)] (hGm : Measurable (G p k w uu)) :
    ∑ b : Fin (2 ^ T₁), ENNReal.ofReal ((2 : ℝ) ^ T₁) * ∑ i ∈ Sblk p k T n γ j T₁ w b,
      ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
        mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩
          Exc p k w uu τ) ≤ mu p k w (Exc p k w uu τ) := by
  have hExc := measurableSet_Exc p k w uu τ hGm
  refine le_trans ?_ (sum_coarse_le (ν p k w) (mu p k w) (Measure.restrict_le_self)
    (Exc p k w uu τ) hExc T₁)
  apply Finset.sum_le_sum
  intro b _
  rw [← Finset.mul_sum, ← mul_assoc]
  have hcount := sum_le_card_image_mul (mu p k w) (Sblk p k T n γ j T₁ w b) j
    (fun i => (Gwit p k T n γ j C u v P a e T₁ w b i ∩ A i ×ˢ univ) ∩ Exc p k w uu τ)
    (Exc p k w uu τ ∩ univ ×ˢ I T₁ b)
    (fun i _ => ((measurableSet_Gwit hC u v P a e T₁ w b i).inter
      ((hA i).prod MeasurableSet.univ)).inter hExc)
    (by
      intro i hi i' hi' hne hjj
      have hγ : γ i = γ i' := ((mem_Sblk.mp hi).1).trans ((mem_Sblk.mp hi').1).symm
      have hAd := hdisj i i' hne hγ hjj
      refine Disjoint.mono (fun q hq => hq.1.2) (fun q hq => hq.1.2) ?_
      exact Set.disjoint_prod.mpr (Or.inl hAd))
    (by
      intro i _ q hq
      refine ⟨hq.2, trivial, ?_⟩
      have hq1 := hq.1.1
      simp only [Gwit, mem_iUnion] at hq1
      obtain ⟨i', hi', hq'⟩ := hq1
      have hi'' := mem_Sblk.mp (Finset.mem_filter.mp hi').1
      exact hi''.2 ((hCsub i' hq').2).2)
  have hcard : (((Sblk p k T n γ j T₁ w b).image j).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (T - T₁)) := by
    rw [ofReal_two_pow]
    have : ((Sblk p k T n γ j T₁ w b).image j).card ≤ 2 ^ (T - T₁) := by
      refine le_trans (Finset.card_le_card ?_) (card_fine_le hT₁ b)
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_Sblk.mp hi).2⟩
    exact_mod_cast this
  calc ENNReal.ofReal ((2 : ℝ) ^ T₁) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
        ∑ i ∈ Sblk p k T n γ j T₁ w b, mu p k w ((Gwit p k T n γ j C u v P a e T₁ w b i ∩
          A i ×ˢ univ) ∩ Exc p k w uu τ)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ T₁) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
          (ENNReal.ofReal ((2 : ℝ) ^ (T - T₁)) * mu p k w (Exc p k w uu τ ∩ univ ×ˢ I T₁ b)) := by
        gcongr
        exact hcount.trans (by gcongr)
    _ = mu p k w (Exc p k w uu τ ∩ univ ×ˢ I T₁ b) := by
        rw [← mul_assoc, ofReal_two_pow_mul_inv hT₁, one_mul]

/-- The non-exceptional parts of the bad witnesses of one world add up to at most `Kc`,
once each is charged to `Kc` times the mass of its source label. -/
lemma cap_sum_le {p : Code} {k T n : ℕ} {γ : Fin n → Fin (W p k)}
    {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set (ℕ × (Fin 5 → ℝ))}
    {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (hCsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) {T₁ : ℕ} (hT₁ : T₁ ≤ T)
    (w : Fin (W p k)) [IsProbabilityMeasure (ν p k w)] (Kc : ℝ) (Z : Fin n → ℝ≥0∞)
    (hZ : ∀ i, γ i = w → ENNReal.ofReal ((2 : ℝ) ^ T₁) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * Z i) ≤
      ENNReal.ofReal Kc * mu p k w (C i)) :
    ∑ b : Fin (2 ^ T₁), ENNReal.ofReal ((2 : ℝ) ^ T₁) * ∑ i ∈ Sblk p k T n γ j T₁ w b,
      ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * Z i ≤ ENNReal.ofReal Kc := by
  simp_rw [Finset.mul_sum]
  calc ∑ b : Fin (2 ^ T₁), ∑ i ∈ Sblk p k T n γ j T₁ w b,
        ENNReal.ofReal ((2 : ℝ) ^ T₁) * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * Z i)
      ≤ ∑ b : Fin (2 ^ T₁), ∑ i ∈ Sblk p k T n γ j T₁ w b,
          ENNReal.ofReal Kc * mu p k w (C i) := by
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro i hi
        exact hZ i (mem_Sblk.mp hi).1
    _ = ∑ i ∈ Finset.univ.filter (fun i => γ i = w), ENNReal.ofReal Kc * mu p k w (C i) :=
        sum_Sblk hT₁ w _
    _ = ENNReal.ofReal Kc * ∑ i ∈ Finset.univ.filter (fun i => γ i = w), mu p k w (C i) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal Kc * 1 := by
        gcongr
        exact sum_mu_C_le_one hC hdisj hCsub w
    _ = ENNReal.ofReal Kc := mul_one _

end Sums

end Submission.Obl.k4_scalar_angular_pair_agreement
