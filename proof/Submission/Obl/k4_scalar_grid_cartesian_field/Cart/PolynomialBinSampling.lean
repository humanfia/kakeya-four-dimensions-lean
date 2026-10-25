-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/PolynomialBinSampling.lean;
-- only the namespace was renamed into o230's.
/- Finite coefficient-bin lists from actual polynomial representatives and
their original measurable witness rows; no posterior time law is used. -/

import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TensorInterpolation
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TimeSampling
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CoefficientBounds
import Submission.Lib.K4IncidenceWitnesses
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory

theorem polynomial_eval_bound_from_samples {D : ℕ} (a : Fin (D + 1) → ℝ)
    (R gap E : ℝ) (hR : 0 ≤ R) (hgap : 0 < gap) (hE : 0 ≤ E)
    (ha : ∀ i, |a i| ≤ R) (hsep : ∀ i j, i ≠ j → gap ≤ |a i - a j|)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ D)
    (hvals : ∀ i, |p.eval (a i)| ≤ E) (t : ℝ) (ht : |t| ≤ R) :
    |p.eval t| ≤ E * (((D : ℝ) + 1) * (2 * R / gap)^D) := by
  classical
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, abs_zero] at h
    exact (not_le_of_gt hgap) h
  rw [polynomial_eval_eq_lagrange a hinj p hp t]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, E * |(Lagrange.basis Finset.univ a i).eval t| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hvals i) (abs_nonneg _)
    _ = E * ∑ i, |(Lagrange.basis Finset.univ a i).eval t| := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (lagrange_weight_sum_bound a R gap hR hgap ha hsep t ht) hE

theorem exists_sample_coefficient_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin (D + 1) → ℝ) (gap E : ℝ),
      0 < gap → 0 ≤ E → (∀ i, a i ∈ Icc (0 : ℝ) 1) →
      (∀ i j, i ≠ j → gap ≤ |a i - a j|) →
      ∀ (p : Polynomial ℝ), p.natDegree ≤ D → (∀ i, |p.eval (a i)| ≤ E) →
      ∀ k, |p.coeff k| ≤ C * E * (((D : ℝ) + 1) * (2 / gap)^D) := by
  obtain ⟨C, hC, hcoeff⟩ := Switching.exists_univariate_coefficient_constant D
  refine ⟨C, hC, ?_⟩
  intro a gap E hgap hE ha hsep p hp hvals k
  have hR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have h := hcoeff p hp (E * (((D : ℝ) + 1) * (2 / gap)^D)) (by positivity)
    (fun t ht => by
      simpa using polynomial_eval_bound_from_samples a 1 gap E (by norm_num) hgap hE
        (fun i => hR _ (ha i)) hsep p hp hvals t (hR t ht)) k
  convert h using 1 <;> ring

theorem coefficient_bins_diameter_from_samples {D : ℕ}
    (C : ℝ) (hcoeff : ∀ (a : Fin (D + 1) → ℝ) (gap E : ℝ),
      0 < gap → 0 ≤ E → (∀ i, a i ∈ Icc (0 : ℝ) 1) →
      (∀ i j, i ≠ j → gap ≤ |a i - a j|) →
      ∀ (p : Polynomial ℝ), p.natDegree ≤ D → (∀ i, |p.eval (a i)| ≤ E) →
      ∀ k, |p.coeff k| ≤ C * E * (((D : ℝ) + 1) * (2 / gap)^D))
    (a : Fin (D + 1) → ℝ) (gap E ε : ℝ) (hgap : 0 < gap) (hE : 0 ≤ E) (hε : 0 < ε)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → gap ≤ |a i - a j|)
    (p p' : Polynomial ℝ) (hp : p.natDegree ≤ D) (hp' : p'.natDegree ≤ D)
    (c c' : Fin (D + 1) → ℤ)
    (hbin : ∀ k : Fin (D + 1), |p.coeff k - ε * (c k : ℝ)| ≤ ε)
    (hbin' : ∀ k : Fin (D + 1), |p'.coeff k - ε * (c' k : ℝ)| ≤ ε)
    (hclose : ∀ i, |p.eval (a i) - p'.eval (a i)| ≤ 2 * E * ε) :
    ∀ k, |(c k : ℝ) - (c' k : ℝ)| ≤
      2 + 2 * C * E * (((D : ℝ) + 1) * (2 / gap)^D) := by
  intro k
  have hd : (p - p').natDegree ≤ D :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hp hp')
  have hsample := hcoeff a gap (2 * E * ε) hgap (by positivity) ha hsep (p - p') hd
    (fun i => by simpa only [Polynomial.eval_sub] using hclose i) k
  rw [Polynomial.coeff_sub] at hsample
  have hfirst : |ε * (c k : ℝ) - p.coeff k| ≤ ε := by
    simpa only [abs_sub_comm] using hbin k
  have htri := (abs_sub_le (ε * (c k : ℝ)) (p.coeff k) (ε * (c' k : ℝ))).trans
    (add_le_add hfirst ((abs_sub_le (p.coeff k) (p'.coeff k) (ε * (c' k : ℝ))).trans
      (add_le_add hsample (hbin' k))))
  rw [← mul_sub, abs_mul, abs_of_pos hε] at htri
  apply (mul_le_mul_iff_right₀ hε).mp
  nlinarith only [htri]

/- At a fixed separated tuple, a list for each sampled value leaves
only a fixed power of the list size many represented coefficient bins. -/
open Classical in
theorem exists_polynomial_sample_list_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin (D + 1) → ℝ) (gap E ε H : ℝ),
      0 < gap → 0 ≤ E → 0 < ε → 0 ≤ H →
      (∀ i, a i ∈ Icc (0 : ℝ) 1) →
      (∀ i j, i ≠ j → gap ≤ |a i - a j|) →
      ∀ (S : Finset (Fin (D + 1) → ℤ)) (p : (Fin (D + 1) → ℤ) → Polynomial ℝ),
      (∀ c ∈ S, (p c).natDegree ≤ D) →
      (∀ c ∈ S, ∀ k : Fin (D + 1), |(p c).coeff k - ε * (c k : ℝ)| ≤ ε) →
      ∀ (L : Fin (D + 1) → Finset ℤ),
      (∀ i, ((L i).card : ℝ) ≤ H) →
      ((S.filter (fun c => ∀ i, ∃ z ∈ L i,
        |(p c).eval (a i) - ε * (z : ℝ)| ≤ E * ε)).card : ℝ) ≤
        H^(D+1) * (7 + 4 * C * E * (((D : ℝ) + 1) * (2 / gap)^D))^(D+1) := by
  classical
  obtain ⟨C, hC, hcoeff⟩ := exists_sample_coefficient_constant D
  refine ⟨C, hC, ?_⟩
  intro a gap E ε H hgap hE hε hH ha hsep S p hp hbin L hL
  let T := S.filter (fun c => ∀ i, ∃ z ∈ L i,
    |(p c).eval (a i) - ε * (z : ℝ)| ≤ E * ε)
  have hT (c : {c // c ∈ T}) (i : Fin (D + 1)) :
      ∃ z ∈ L i, |(p c).eval (a i) - ε * (z : ℝ)| ≤ E * ε :=
    (Finset.mem_filter.mp c.property).2 i
  choose q hq hfit using hT
  let f : (Fin (D + 1) → ℤ) → (Fin (D + 1) → ℤ) :=
    fun c => if hc : c ∈ T then q ⟨c, hc⟩ else 0
  have hf (c : Fin (D + 1) → ℤ) (hc : c ∈ T) :
      (∀ i, f c i ∈ L i) ∧
        (∀ i, |(p c).eval (a i) - ε * (f c i : ℝ)| ≤ E * ε) := by
    constructor
    · intro i
      simpa only [f, dite_eq_left hc] using hq ⟨c, hc⟩ i
    · intro i
      simpa only [f, dite_eq_left hc] using hfit ⟨c, hc⟩ i
  let Q := Fintype.piFinset L
  have hmap : (T : Set (Fin (D + 1) → ℤ)).MapsTo f Q := by
    intro c hc
    exact Fintype.mem_piFinset.mpr (hf c hc).1
  let R := 2 + 2 * C * E * (((D : ℝ) + 1) * (2 / gap)^D)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfiber (z : Fin (D + 1) → ℤ) :
      ((T.filter (fun c => f c = z)).card : ℝ) ≤ (2 * R + 3)^(D+1) := by
    suffices hd : ∀ c ∈ T.filter (fun c => f c = z),
        ∀ c' ∈ T.filter (fun c => f c = z), ∀ k,
        |(c k : ℝ) - (c' k : ℝ)| ≤ R by
      simpa only [Fintype.card_fin] using
        Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter _ hR hd
    intro c hc c' hc' k
    obtain ⟨hcT, hcz⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc'T, hc'z⟩ := Finset.mem_filter.mp hc'
    have hcS := (Finset.mem_filter.mp hcT).1
    have hc'S := (Finset.mem_filter.mp hc'T).1
    apply coefficient_bins_diameter_from_samples C hcoeff a gap E ε hgap hE hε ha hsep
      (p c) (p c') (hp c hcS) (hp c' hc'S) c c' (hbin c hcS) (hbin c' hc'S) _ k
    intro i
    have hcfit := (hf c hcT).2 i
    have hc'fit := (hf c' hc'T).2 i
    rw [hcz] at hcfit
    rw [hc'z] at hc'fit
    have ht := (abs_sub_le ((p c).eval (a i)) (ε * (z i : ℝ)) ((p c').eval (a i))).trans
      (add_le_add hcfit (by simpa only [abs_sub_comm] using hc'fit))
    linarith
  have hQ : (Q.card : ℝ) ≤ H^(D+1) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin (D + 1), H :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hL i)
      _ = H^(D+1) := by simp
  have hcount : (T.card : ℝ) = ∑ z ∈ Q, ((T.filter (fun c => f c = z)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  change (T.card : ℝ) ≤ _
  calc
    _ = ∑ z ∈ Q, ((T.filter (fun c => f c = z)).card : ℝ) := hcount
    _ ≤ ∑ _z ∈ Q, (2 * R + 3)^(D+1) := Finset.sum_le_sum fun z _ => hfiber z
    _ = (Q.card : ℝ) * (2 * R + 3)^(D+1) := by simp
    _ ≤ H^(D+1) * (2 * R + 3)^(D+1) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by congr 2; dsimp [R]; ring

/-- One representative per actual coefficient bin, each with its own
original long witness row, gives a finite polynomial list. All times
are sampled from the same original uniform block law. -/
theorem exists_original_polynomial_bin_count_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (gap η E ε H : ℝ),
      0 < gap → 0 ≤ η → 0 ≤ E → 0 < ε → 0 ≤ H →
      ((D : ℝ) + 1)^2 * (2 * gap) ≤ η^(D+1) / 2 →
      ∀ (S : Finset (Fin (D + 1) → ℤ)) (p : (Fin (D + 1) → ℤ) → Polynomial ℝ),
      (∀ c ∈ S, (p c).natDegree ≤ D) →
      (∀ c ∈ S, ∀ k : Fin (D + 1), |(p c).coeff k - ε * (c k : ℝ)| ≤ ε) →
      ∀ (A : (Fin (D + 1) → ℤ) → Set ℝ),
      (∀ c ∈ S, MeasurableSet (A c)) →
      (∀ c ∈ S, A c ⊆ Icc (0 : ℝ) 1) →
      (∀ c ∈ S, ENNReal.ofReal η ≤ MeasureTheory.volume (A c)) →
      ∀ (L : ℝ → Finset ℤ), (∀ t ∈ Icc (0 : ℝ) 1, ((L t).card : ℝ) ≤ H) →
      (∀ c ∈ S, ∀ t ∈ A c, ∃ z ∈ L t,
        |(p c).eval t - ε * (z : ℝ)| ≤ E * ε) →
      (S.card : ℝ) * (η^(D+1) / 2) ≤
        H^(D+1) * (7 + 4 * C * E * (((D : ℝ) + 1) * (2 / gap)^D))^(D+1) := by
  classical
  obtain ⟨C, hC, hpoint⟩ := exists_polynomial_sample_list_constant D
  refine ⟨C, hC, ?_⟩
  intro gap η E ε H hgap hη hE hε hH hcollision S p hp hbin A hAm hAunit hAlength L hL hfit
  let B := H^(D+1) * (7 + 4 * C * E * (((D : ℝ) + 1) * (2 / gap)^D))^(D+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Icc (0 : ℝ) 1)
  letI : MeasureTheory.IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  let μ := MeasureTheory.Measure.pi (fun _ : Fin (D + 1) => ν)
  let events : S → Set (Fin (D + 1) → ℝ) :=
    fun c => separatedTimeEvent (D + 1) (A c) gap
  have hmeas (c : S) : MeasurableSet (events c) :=
    measurableSet_separatedTimeEvent (D + 1) (A c) (hAm c c.property) gap
  have hlower (c : S) : ENNReal.ofReal (η^(D+1) / 2) ≤ μ (events c) := by
    apply original_uniform_time_separated_lower (D + 1) gap η hη hgap.le
      (A c) (hAm c c.property) (hAunit c c.property) (hAlength c c.property)
    simpa only [Nat.cast_add, Nat.cast_one] using hcollision
  have hcount (x : Fin (D + 1) → ℝ) :
      ((Finset.univ.filter (fun c : S => x ∈ events c)).card : ℝ) ≤ B := by
    by_cases hxunit : ∀ i, x i ∈ Icc (0 : ℝ) 1
    · by_cases hxsep : Pairwise (fun i j => gap ≤ |x i - x j|)
      · let T := S.filter (fun c => ∀ i, ∃ z ∈ L (x i),
          |(p c).eval (x i) - ε * (z : ℝ)| ≤ E * ε)
        have hmap : (↑(Finset.univ.filter (fun c : S => x ∈ events c)) : Set S).MapsTo
            Subtype.val T := by
          intro c hc
          have hcgood := (Finset.mem_filter.mp hc).2
          apply Finset.mem_filter.mpr
          refine ⟨c.property, ?_⟩
          intro i
          exact hfit c c.property (x i) (hcgood.1 i)
        have hcard := Finset.card_le_card_of_injOn Subtype.val hmap
          (fun c _ c' _ hc => Subtype.ext hc)
        apply (Nat.cast_le.mpr hcard).trans
        exact hpoint x gap E ε H hgap hE hε hH hxunit hxsep S p hp hbin
          (fun i => L (x i)) (fun i => hL (x i) (hxunit i))
      · have hnone : ∀ c : S, x ∉ events c := by
          intro c hc
          exact hxsep hc.2
        simpa only [hnone, Finset.filter_false, Finset.card_empty, Nat.cast_zero] using hB
    · have hnone : ∀ c : S, x ∉ events c := by
        intro c hc
        exact hxunit (fun i => hAunit c c.property (hc.1 i))
      simpa only [hnone, Finset.filter_false, Finset.card_empty, Nat.cast_zero] using hB
  have hfinal := finite_sampling_count μ events hmeas (η^(D+1) / 2) B
    (by positivity) hB hlower hcount
  simpa only [Fintype.card_coe] using hfinal

/-- The separated-time gap is chosen explicitly from the original row
length. The resulting bin count has fixed polynomial dependence on all
loss parameters, independently of the number of representatives. -/
theorem exists_polynomial_bin_count_from_original_rows_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η E ε H : ℝ),
      0 < η → 0 ≤ E → 0 < ε → 0 ≤ H →
      ∀ (S : Finset (Fin (D + 1) → ℤ)) (p : (Fin (D + 1) → ℤ) → Polynomial ℝ),
      (∀ c ∈ S, (p c).natDegree ≤ D) →
      (∀ c ∈ S, ∀ k : Fin (D + 1), |(p c).coeff k - ε * (c k : ℝ)| ≤ ε) →
      ∀ (A : (Fin (D + 1) → ℤ) → Set ℝ),
      (∀ c ∈ S, MeasurableSet (A c)) →
      (∀ c ∈ S, A c ⊆ Icc (0 : ℝ) 1) →
      (∀ c ∈ S, ENNReal.ofReal η ≤ volume (A c)) →
      ∀ (L : ℝ → Finset ℤ), (∀ t ∈ Icc (0 : ℝ) 1, ((L t).card : ℝ) ≤ H) →
      (∀ c ∈ S, ∀ t ∈ A c, ∃ z ∈ L t,
        |(p c).eval t - ε * (z : ℝ)| ≤ E * ε) →
      (S.card : ℝ) ≤ (2 / η^(D+1)) * H^(D+1) *
        (7 + 4 * C * E * (((D : ℝ) + 1) *
          (8 * ((D : ℝ) + 1)^2 / η^(D+1))^D))^(D+1) := by
  obtain ⟨C, hC, hcount⟩ := exists_original_polynomial_bin_count_constant D
  refine ⟨C, hC, ?_⟩
  intro η E ε H hη hE hε hH S p hp hbin A hAm hAunit hAlength L hL hfit
  let gap := η^(D+1) / (4 * ((D : ℝ) + 1)^2)
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hn : (D : ℝ) + 1 ≠ 0 := by positivity
  have hηpow : η^(D+1) ≠ 0 := by positivity
  have hcollision : ((D : ℝ) + 1)^2 * (2 * gap) ≤ η^(D+1) / 2 := by
    have heq : ((D : ℝ) + 1)^2 * (2 * gap) = η^(D+1) / 2 := by
      dsimp [gap]
      field_simp
      <;> ring
    exact heq.le
  have h := hcount gap η E ε H hgap hη.le hE hε hH hcollision
    S p hp hbin A hAm hAunit hAlength L hL hfit
  have hgap_eq : 2 / gap = 8 * ((D : ℝ) + 1)^2 / η^(D+1) := by
    dsimp [gap]
    field_simp
    <;> ring
  have hq : 0 < η^(D+1) / 2 := by positivity
  calc
    (S.card : ℝ) ≤ (H^(D+1) *
        (7 + 4 * C * E * (((D : ℝ) + 1) * (2 / gap)^D))^(D+1)) / (η^(D+1) / 2) :=
      (le_div_iff₀ hq).mpr h
    _ = _ := by rw [hgap_eq]; ring

/-- The same count for genuine floor bins of all normalized-time
coefficients, using the accepted scaled-floor error estimate. -/
theorem exists_polynomial_floor_bin_count_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η E ε H : ℝ),
      0 < η → 0 ≤ E → 0 < ε → 0 ≤ H →
      ∀ (S : Finset (Fin (D + 1) → ℤ)) (p : (Fin (D + 1) → ℤ) → Polynomial ℝ),
      (∀ c ∈ S, (p c).natDegree ≤ D) →
      (∀ c ∈ S, ∀ k : Fin (D + 1), ⌊(p c).coeff k / ε⌋ = c k) →
      ∀ (A : (Fin (D + 1) → ℤ) → Set ℝ),
      (∀ c ∈ S, MeasurableSet (A c)) →
      (∀ c ∈ S, A c ⊆ Icc (0 : ℝ) 1) →
      (∀ c ∈ S, ENNReal.ofReal η ≤ volume (A c)) →
      ∀ (L : ℝ → Finset ℤ), (∀ t ∈ Icc (0 : ℝ) 1, ((L t).card : ℝ) ≤ H) →
      (∀ c ∈ S, ∀ t ∈ A c, ∃ z ∈ L t,
        |(p c).eval t - ε * (z : ℝ)| ≤ E * ε) →
      (S.card : ℝ) ≤ (2 / η^(D+1)) * H^(D+1) *
        (7 + 4 * C * E * (((D : ℝ) + 1) *
          (8 * ((D : ℝ) + 1)^2 / η^(D+1))^D))^(D+1) := by
  obtain ⟨C, hC, hcount⟩ := exists_polynomial_bin_count_from_original_rows_constant D
  refine ⟨C, hC, ?_⟩
  intro η E ε H hη hE hε hH S p hp hcode A hAm hAunit hAlength L hL hfit
  apply hcount η E ε H hη hE hε hH S p hp _ A hAm hAunit hAlength L hL hfit
  intro c hc k
  rw [← hcode c hc k]
  exact Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hε ((p c).coeff k)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
