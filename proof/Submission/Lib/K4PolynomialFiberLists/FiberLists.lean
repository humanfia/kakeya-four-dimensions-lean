/-
Adapted from: here:o106
Original proofs by session x0352, commit e08f59f4.
Owned source: Submission/Obl/k4_isotropic_path_improvement/PolynomialFiberLists.lean.
-/

import Submission.Lib.K4PolynomialRemez
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Lib.K4VelocityStrips.StripPacking
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Lib.K4PolynomialFiberLists.LocalListPacking

/-!
Coefficient lists for polynomial fits with substantial original witness
sets and short value lists at each time. All counts refer to actual fits.
-/

namespace Submission.Lib.K4PolynomialFiberLists

open MeasureTheory Set

noncomputable section

private theorem finite_separated_coefficient_net {ι E : Type*} [PseudoMetricSpace E] (F : Finset ι) (v : ι → E)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Finset ι, S ⊆ F ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → r < dist (v i) (v j)) ∧
      ∀ i ∈ F, ∃ j ∈ S, dist (v i) (v j) ≤ r := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨S, hSF, hsep, hcover⟩ := ih
    by_cases hc : ∃ j ∈ S, dist (v a) (v j) ≤ r
    · refine ⟨S, hSF.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hc
      · exact hcover i hi
    · have hdist (j : ι) (hj : j ∈ S) : r < dist (v a) (v j) := by
        exact lt_of_not_ge (fun h => hc ⟨j, hj, h⟩)
      refine ⟨insert a S, Finset.insert_subset_insert _ hSF, ?_, ?_⟩
      · intro i hi j hj hij
        by_cases hia : i = a
        · subst i
          exact hdist j ((Finset.mem_insert.mp hj).resolve_left (Ne.symm hij))
        · have hiS : i ∈ S := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            simpa only [dist_comm] using hdist i hiS
          · exact hsep i hiS j ((Finset.mem_insert.mp hj).resolve_left hja) hij
      · intro i hi
        by_cases hia : i = a
        · subst i
          exact ⟨a, Finset.mem_insert_self _ _, by simpa using hr⟩
        · obtain ⟨j, hj, hij⟩ := hcover i ((Finset.mem_insert.mp hi).resolve_left hia)
          exact ⟨j, Finset.mem_insert_of_mem hj, hij⟩


/-- The accepted multivariate real-box comparison in one variable. -/
theorem exists_univariate_coefficient_bound (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ k : ℕ, |p.coeff k| ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube 1 D
  refine ⟨C, hC, ?_⟩
  intro p hp E hE hb k
  let q := (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p
  have hdeg : q.totalDegree ≤ D := by
    apply Finset.sup_le
    intro d hd
    have hc : p.coeff (d default) ≠ 0 := by
      simpa only [q, MvPolynomial.mem_support_iff,
        MvPolynomial.coeff_uniqueAlgEquiv_symm] using hd
    calc
      d.sum (fun _ e => e) = d default := by
        conv_lhs => rw [Finsupp.unique_single d]
        simp
      _ ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hc
      _ ≤ D := hp
  have heval (x : Fin 1 → ℝ) : MvPolynomial.eval x q = p.eval (x default) :=
    MvPolynomial.eval₂_uniqueAlgEquiv_symm
  have hq := hbound q hdeg E hE (fun x hx => by
    rw [heval]
    exact hb _ ⟨hx.1 _, hx.2 _⟩) (Finsupp.single default k)
  simpa only [q, MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same] using hq

/-- An original positive-volume time witness controls every coefficient.
Only the accepted Remez comparison and real-box coefficient bound enter. -/
theorem coefficient_bound_of_unit_witness (D : ℕ) (C : ℝ)
    (hC : ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ k : ℕ, |p.coeff k| ≤ C * E)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ D) (S : Set ℝ)
    (η E : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |p.eval t| ≤ E) :
    ∀ k : ℕ, |p.coeff k| ≤ C * (8 * ((D : ℝ) + 1) / η) ^ D * E := by
  have hb := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit p D hp S
    hη hη₁ hE hS hmass hbound
  intro k
  exact (hC p hp _ (by positivity) hb k).trans_eq (by ring)

/-- Coefficient separation forces a small set of times at which two
polynomials can occupy the same value bin. -/
theorem polynomial_sublevel_mass_lt (D : ℕ) (C : ℝ)
    (hC : ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ k : ℕ, |p.coeff k| ≤ C * E)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ D)
    (η E : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (hE : 0 ≤ E)
    (hsep : ∃ k : ℕ, C * (8 * ((D : ℝ) + 1) / η) ^ D * E < |p.coeff k|) :
    volume (Icc (0 : ℝ) 1 ∩ {t | |p.eval t| ≤ E}) < ENNReal.ofReal η := by
  by_contra h
  have hm := le_of_not_gt h
  obtain ⟨k, hk⟩ := hsep
  have hb := coefficient_bound_of_unit_witness D C hC p hp
    (Icc (0 : ℝ) 1 ∩ {t | |p.eval t| ≤ E}) η E hη hη₁ hE
    inter_subset_left hm (fun _ ht => ht.2) k
  exact (not_lt_of_ge hb) hk

open Classical in
/-- A separated family of actual polynomial fits is short when its
ordinary witness sets are substantial and each time has few value bins.
The bound does not involve the global number of value bins. -/
theorem polynomial_fit_packing {ι : Type*} [Fintype ι] {q : ℕ}
    (D : ℕ) (C : ℝ)
    (hC : ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ k : ℕ, |p.coeff k| ≤ C * E)
    (P : ι → Fin q → Polynomial ℝ) (hP : ∀ i j, (P i j).natDegree ≤ D)
    (S : ι → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (hSunit : ∀ i, S i ⊆ Icc (0 : ℝ) 1)
    (p K η δ : ℝ) (hp : 0 < p) (hK : 0 < K)
    (hη : 0 < η) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hmass : ∀ i, ENNReal.ofReal η ≤ volume (S i))
    (hlocal : ∀ t,
      (((Finset.univ.filter fun i => t ∈ S i).image
        (fun i => fun j : Fin q => ⌊(P i j).eval t / p⌋)).card : ℝ) ≤ K)
    (hsep : ∀ i i', i ≠ i' → ∃ j : Fin q, ∃ k : ℕ,
      C * (8 * ((D : ℝ) + 1) / δ) ^ D * p < |(P i j).coeff k - (P i' j).coeff k|)
    (hsmall : 2 * K * δ ≤ η ^ 2) :
    (Fintype.card ι : ℝ) ≤ 2 * K / η ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let code : ι → ℝ → Fin q → ℤ := fun i t j => ⌊(P i j).eval t / p⌋
  have hmcode (i : ι) : Measurable (code i) := by
    apply Measurable.of_eval
    intro j
    exact ((P i j).continuous.measurable.div_const p).floor
  have hreal (i : ι) : η ≤ μ.real (S i) := by
    have heq : μ (S i) = volume (S i) := by
      rw [Measure.restrict_apply (hS i), inter_eq_left.mpr (hSunit i)]
    have hle : ENNReal.ofReal η ≤ μ (S i) := by rw [heq]; exact hmass i
    have h := ENNReal.toReal_mono (measure_ne_top μ (S i)) hle
    simpa only [ENNReal.toReal_ofReal hη.le, measureReal_def] using h
  apply local_list_heavy_family_card μ S hS code
    (fun i i' => measurableSet_eq_fun (hmcode i) (hmcode i')) K η δ hK hη hδ.le hlocal hreal
    ?_ hsmall
  intro i i' hii'
  obtain ⟨j, k, hcoef⟩ := hsep i i' hii'
  let Q := P i j - P i' j
  have hdeg : Q.natDegree ≤ D :=
    (Polynomial.natDegree_sub_le (P i j) (P i' j)).trans (max_le (hP i j) (hP i' j))
  have hsublevel : volume (Icc (0 : ℝ) 1 ∩ {t | |Q.eval t| ≤ p}) < ENNReal.ofReal δ := by
    apply polynomial_sublevel_mass_lt D C hC Q hdeg δ p hδ hδ₁ hp.le
    exact ⟨k, by simpa only [Q, Polynomial.coeff_sub] using hcoef⟩
  let A := {t | t ∈ S i ∧ t ∈ S i' ∧ code i t = code i' t}
  have hA : MeasurableSet A :=
    (hS i).inter ((hS i').inter (measurableSet_eq_fun (hmcode i) (hmcode i')))
  have hsub : A ⊆ Icc (0 : ℝ) 1 ∩ {t | |Q.eval t| ≤ p} := by
    intro t ht
    refine ⟨hSunit i ht.1, ?_⟩
    have hfloor : ⌊(P i j).eval t / p⌋ = ⌊(P i' j).eval t / p⌋ := congrFun ht.2.2 j
    have h := Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    rw [← sub_div, abs_div, abs_of_pos hp] at h
    have hh := (div_lt_one hp).mp h
    change |Q.eval t| ≤ p
    simpa only [Q, Polynomial.eval_sub] using hh.le
  have hμ : μ A ≤ ENNReal.ofReal δ := by
    calc
      μ A ≤ volume A := Measure.restrict_le_self _
      _ ≤ volume (Icc (0 : ℝ) 1 ∩ {t | |Q.eval t| ≤ p}) := measure_mono hsub
      _ ≤ ENNReal.ofReal δ := hsublevel.le
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ).trans_eq
    (ENNReal.toReal_ofReal hδ.le)

/-- Flatten the finitely many row coefficients through degree D. -/
def polynomialFitCoefficients {q : ℕ} (D : ℕ) (P : Fin q → Polynomial ℝ) :
    Fin (q * (D + 1)) → ℝ := fun a =>
  (P (finProdFinEquiv.symm a).1).coeff (finProdFinEquiv.symm a).2

def polynomialFitCoefficientCode {q : ℕ} (D : ℕ) (p : ℝ)
    (P : Fin q → Polynomial ℝ) : Fin (q * (D + 1)) → ℤ :=
  fun a => ⌊polynomialFitCoefficients D P a / p⌋

def fiberFitConditioning (D : ℕ) (C δ : ℝ) : ℝ :=
  C * (8 * ((D : ℝ) + 1) / δ) ^ D

open Classical in
/-- A short per-time value list bounds the ACTUAL coefficient-bin image
of every finite family with original witness duration eta. The constant
depends on degree, duration and local list cost, but not on the family
size, coefficient magnitude or fine mesh p. -/
theorem polynomial_fit_coefficient_bins {ι : Type*} [Fintype ι] {q : ℕ}
    (D : ℕ) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ k : ℕ, |p.coeff k| ≤ C * E)
    (P : ι → Fin q → Polynomial ℝ) (hP : ∀ i j, (P i j).natDegree ≤ D)
    (E : ι → Set ℝ) (hE : ∀ i, MeasurableSet (E i))
    (hEunit : ∀ i, E i ⊆ Icc (0 : ℝ) 1)
    (p K η δ : ℝ) (hp : 0 < p) (hK : 0 < K)
    (hη : 0 < η) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hmass : ∀ i, ENNReal.ofReal η ≤ volume (E i))
    (hlocal : ∀ t,
      (((Finset.univ.filter fun i => t ∈ E i).image
        (fun i => fun j : Fin q => ⌊(P i j).eval t / p⌋)).card : ℝ) ≤ K)
    (hsmall : 2 * K * δ ≤ η ^ 2) :
    ((Finset.univ.image (fun i => polynomialFitCoefficientCode D p (P i))).card : ℝ) ≤
      (2 * K / η ^ 2) *
        ((2 * ⌈fiberFitConditioning D C δ⌉₊ + 1 : ℕ) : ℝ) ^ (q * (D + 1)) := by
  let H := fiberFitConditioning D C δ
  let v : ι → Fin (q * (D + 1)) → ℝ := fun i => polynomialFitCoefficients D (P i)
  have hH : 0 ≤ H := by dsimp [H, fiberFitConditioning]; positivity
  obtain ⟨S, -, hsep, hcover⟩ := finite_separated_coefficient_net Finset.univ v
    (H * p) (mul_nonneg hH hp.le)
  have hsepP : ∀ i i' : S, i ≠ i' → ∃ j : Fin q, ∃ k : ℕ,
      C * (8 * ((D : ℝ) + 1) / δ) ^ D * p <
        |(P i j).coeff k - (P i' j).coeff k| := by
    intro i i' hii'
    have hdist : H * p < dist (v i) (v i') :=
      hsep i i.property i' i'.property (fun heq => hii' (Subtype.ext heq))
    have hex : ∃ a, H * p < |v i a - v i' a| := by
      by_contra! hn
      have hd : dist (v i) (v i') ≤ H * p :=
        (dist_pi_le_iff (mul_nonneg hH hp.le)).mpr fun a =>
          by simpa only [Real.dist_eq] using hn a
      exact (not_le_of_gt hdist) hd
    obtain ⟨a, ha⟩ := hex
    exact ⟨(finProdFinEquiv.symm a).1, (finProdFinEquiv.symm a).2, ha⟩
  have hlocalS (t : ℝ) :
      (((Finset.univ.filter fun i : S => t ∈ E i).image
        (fun i : S => fun j : Fin q => ⌊(P i j).eval t / p⌋)).card : ℝ) ≤ K := by
    let A := (Finset.univ.filter fun i : S => t ∈ E i).image
      (fun i : S => fun j : Fin q => ⌊(P i j).eval t / p⌋)
    let B := (Finset.univ.filter fun i : ι => t ∈ E i).image
      (fun i : ι => fun j : Fin q => ⌊(P i j).eval t / p⌋)
    have hsub : A ⊆ B := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨i.val,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, rfl⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hlocal t)
  have hScard : (S.card : ℝ) ≤ 2 * K / η ^ 2 := by
    simpa only [Fintype.card_coe] using polynomial_fit_packing (ι := S) (q := q) D C hC
      (fun i : S => P i) (fun i j => hP i j)
      (fun i : S => E i) (fun i => hE i) (fun i => hEunit i)
      p K η δ hp hK hη hδ hδ₁ (fun i => hmass i) hlocalS hsepP hsmall
  let L := S.biUnion fun j => Submission.Lib.K4ListedExceptions.integerCodeBox ⌈H⌉₊
    (polynomialFitCoefficientCode D p (P j))
  have hcoverCode : Finset.univ.image (fun i => polynomialFitCoefficientCode D p (P i)) ⊆ L := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, hij⟩ := hcover i (Finset.mem_univ _)
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, ?_⟩
    apply Submission.Lib.K4ListedExceptions.floor_code_mem_integerCodeBox ⌈H⌉₊
      (v i) (v j) (fun _ => p) (fun _ => hp)
    intro a
    have ha := (dist_pi_le_iff (mul_nonneg hH hp.le)).mp hij a
    have ha' : |v i a - v j a| ≤ H * p := by simpa only [Real.dist_eq] using ha
    exact ha'.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil H) hp.le)
  have hLcard : (L.card : ℝ) ≤ (S.card : ℝ) *
      ((2 * ⌈H⌉₊ + 1 : ℕ) : ℝ) ^ (q * (D + 1)) := by
    have hnat : L.card ≤ S.card * (2 * ⌈H⌉₊ + 1) ^ (q * (D + 1)) := by
      calc
        L.card ≤ ∑ j ∈ S,
            (Submission.Lib.K4ListedExceptions.integerCodeBox ⌈H⌉₊
              (polynomialFitCoefficientCode D p (P j))).card := Finset.card_biUnion_le
        _ = _ := by simp only [Submission.Lib.K4ListedExceptions.card_integerCodeBox,
          Finset.sum_const_nat]
    exact_mod_cast hnat
  exact (Nat.cast_le.mpr (Finset.card_le_card hcoverCode)).trans
    (hLcard.trans (mul_le_mul_of_nonneg_right hScard (by positivity)))

open Classical in
/-- The fiber list costs a fixed power of the common budget K. The
constant is uniform before every finite family and every mesh p. -/
theorem polynomial_fit_list_power_bound (D q : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ι : Type) [Fintype ι]
      (P : ι → Fin q → Polynomial ℝ), (∀ i j, (P i j).natDegree ≤ D) →
      ∀ (E : ι → Set ℝ), (∀ i, MeasurableSet (E i)) →
      (∀ i, E i ⊆ Icc (0 : ℝ) 1) → ∀ p K : ℝ, 0 < p → 1 ≤ K →
      (∀ i, ENNReal.ofReal (1 / K) ≤ volume (E i)) →
      (∀ t, (((Finset.univ.filter fun i => t ∈ E i).image
        (fun i => fun j : Fin q => ⌊(P i j).eval t / p⌋)).card : ℝ) ≤ K) →
      ((Finset.univ.image (fun i => polynomialFitCoefficientCode D p (P i))).card : ℝ) ≤
        A * K ^ (3 + 3 * D * (q * (D + 1))) := by
  obtain ⟨C, hCpos, hC⟩ := exists_univariate_coefficient_bound D
  let n := q * (D + 1)
  let B := 2 * C * (32 * ((D : ℝ) + 1)) ^ D + 3
  refine ⟨2 * B ^ n, by dsimp [B]; positivity, ?_⟩
  intro ι _ P hP E hE hEunit p K hp hK hmass hlocal
  have hKpos : 0 < K := by linarith
  let δ := 1 / (4 * K ^ 3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 * K ^ 3)).mpr
    nlinarith [(show 1 ≤ K ^ 3 from one_le_pow₀ hK)]
  have hsmall : 2 * K * δ ≤ (1 / K) ^ 2 := by
    have heq : 2 * K * δ = (1 / K) ^ 2 / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    nlinarith [sq_nonneg (1 / K)]
  have hcount := polynomial_fit_coefficient_bins D C hCpos hC P hP E hE hEunit
    p K (1 / K) δ hp hKpos (by positivity) hδ hδ₁ hmass hlocal hsmall
  have hcondition : fiberFitConditioning D C δ =
      C * (32 * ((D : ℝ) + 1)) ^ D * K ^ (3 * D) := by
    have hbase : 8 * ((D : ℝ) + 1) / δ = (32 * ((D : ℝ) + 1)) * K ^ 3 := by
      dsimp [δ]
      field_simp
      ring
    rw [fiberFitConditioning, hbase, mul_pow, ← pow_mul]
    ring
  have hceil : ((2 * ⌈fiberFitConditioning D C δ⌉₊ + 1 : ℕ) : ℝ) ≤ B * K ^ (3 * D) := by
    have hnonneg : 0 ≤ fiberFitConditioning D C δ := by
      rw [hcondition]
      positivity
    have hc := Nat.ceil_lt_add_one hnonneg
    have hk : 1 ≤ K ^ (3 * D) := one_le_pow₀ hK
    rw [hcondition] at hc
    rw [hcondition]
    push_cast
    dsimp only [B]
    nlinarith
  have hfactor : 2 * K / (1 / K) ^ 2 = 2 * K ^ 3 := by field_simp
  calc
    _ ≤ (2 * K / (1 / K) ^ 2) *
        ((2 * ⌈fiberFitConditioning D C δ⌉₊ + 1 : ℕ) : ℝ) ^ n := hcount
    _ ≤ (2 * K ^ 3) * (B * K ^ (3 * D)) ^ n := by
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hceil n) (by positivity)
    _ = (2 * B ^ n) * (K ^ 3 * K ^ ((3 * D) * n)) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ = (2 * B ^ n) * K ^ (3 + 3 * D * (q * (D + 1))) := by rw [pow_add]

end

end Submission.Lib.K4PolynomialFiberLists
