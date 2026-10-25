import Submission.Obl.k4_matching_cofinal_palette_selection.Data
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode
import Submission.Obl.k4_matching_cofinal_palette_selection.Palette

namespace Submission.Obl.k4_matching_cofinal_palette_selection

open MeasureTheory Set
open scoped ENNReal

noncomputable def badMass {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (C k : ℕ) (R : ℝ) : ℝ≥0∞ :=
  μ {x | x ∈ S ∧ R * supportLikelihood μ S F Z k x <
    supportLikelihood μ S F Z (k + C) x}

theorem supportLikelihood_comp {Ω Ζ Ζ' : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (e : Ζ → Ζ') (he : Function.Injective e) (k : ℕ) (x : Ω) :
    supportLikelihood μ S F (e ∘ Z) k x = supportLikelihood μ S F Z k x := by
  simp only [supportLikelihood, Function.comp_apply, he.eq_iff]

theorem supportLikelihood_eq_code {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (Z : Ω → ℕ)
    {n : ℕ} (X : Ω → Fin n) (G : ℕ → Fin n → ℕ) (W : Fin n → ℕ)
    (k t : ℕ) (x : Ω) (hx : x ∈ S)
    (hF : ∀ y ∈ S, G t (X y) = F k y) (hZ : ∀ y ∈ S, W (X y) = Z y) :
    supportLikelihood μ S F Z k x = eventLikelihood μ X G W t x := by
  have hae : ∀ᵐ y ∂μ, y ∈ S := ae_iff.mpr hμS
  have hnum : μ {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x} =
      μ {y | G t (X y) = G t (X x) ∧ W (X y) = W (X x)} := by
    apply measure_congr
    filter_upwards [hae] with y hy
    simp only [hy, true_and, hF y hy, hF x hx, hZ y hy, hZ x hx]
  have hden : μ {y | y ∈ S ∧ F k y = F k x} =
      μ {y | G t (X y) = G t (X x)} := by
    apply measure_congr
    filter_upwards [hae] with y hy
    simp only [hy, true_and, hF y hy, hF x hx]
  simp only [supportLikelihood, eventLikelihood, measureReal_def, hnum, hden]

theorem failureMass_eq_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (X : Ω → Fin n) (hX : Measurable X)
    (G : ℕ → Fin n → ℕ) (W : Fin n → ℕ) (C a : ℕ) (R : ℝ) :
    likelihoodFailureMass (atomMass μ X) G W C a R =
      μ.real {x | R * eventLikelihood μ X G W a x < eventLikelihood μ X G W (a + C) x} := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i =>
        R * likelihood (atomMass μ X) G W a i < likelihood (atomMass μ X) G W (a + C) i),
        atomMass μ X i := by
      unfold likelihoodFailureMass
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hp : 0 < atomMass μ X i
      · simp [hp]
      · have hz : atomMass μ X i = 0 := le_antisymm (le_of_not_gt hp) (atomMass_nonneg μ X i)
        simp [hz]
    _ = _ := by
      rw [sum_atomMass μ X hX]
      congr 1
      ext x
      simp only [mem_preimage, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred_eq, eventLikelihood_eq μ X hX]

theorem badMass_eq_failureMass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (Z : Ω → ℕ)
    {n : ℕ} (X : Ω → Fin n) (hX : Measurable X)
    (G : ℕ → Fin n → ℕ) (W : Fin n → ℕ)
    (k a C : ℕ) (R : ℝ)
    (hF : ∀ y ∈ S, G a (X y) = F k y)
    (hFC : ∀ y ∈ S, G (a + C) (X y) = F (k + C) y)
    (hZ : ∀ y ∈ S, W (X y) = Z y) :
    (badMass μ S F Z C k R).toReal = likelihoodFailureMass (atomMass μ X) G W C a R := by
  rw [failureMass_eq_event μ X hX]
  simp only [badMass, measureReal_def]
  congr 1
  apply measure_congr
  have hae : ∀ᵐ y ∂μ, y ∈ S := ae_iff.mpr hμS
  filter_upwards [hae] with x hx
  simp only [hx, true_and,
    supportLikelihood_eq_code μ S hμS F Z X G W k a x hx hF hZ,
    supportLikelihood_eq_code μ S hμS F Z X G W (k + C) (a + C) x hx hFC hZ]

/-- Finite records and finite palettes on each record fiber give a finite total palette. -/
theorem finite_palette_range {Ω Ζ : Type*} (S : Set Ω) (f : Ω → ℕ) (Z : Ω → Ζ)
    (hf : (f '' S).Finite)
    (hZ : ∀ x ∈ S, (Z '' {y | y ∈ S ∧ f y = f x}).Finite) : (Z '' S).Finite := by
  have h : (⋃ b ∈ f '' S, Z '' {y | y ∈ S ∧ f y = b}).Finite := by
    apply hf.biUnion
    rintro b ⟨x, hx, rfl⟩
    exact hZ x hx
  apply h.subset
  rintro _ ⟨x, hx, rfl⟩
  exact mem_iUnion.mpr ⟨f x, mem_iUnion.mpr ⟨⟨x, hx, rfl⟩, ⟨x, ⟨hx, rfl⟩, rfl⟩⟩⟩

/-- The finite palette estimate bounds bad continuous steps, after shifting to a
common reference record and extending the finite filtration constantly. -/
theorem continuous_bad_steps_bound (hpal : PaletteEstimate)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (Z : Ω → ℕ) (q z C M : ℕ)
    (hzq : z ≤ q) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hFm : ∀ k, k ≤ q → Measurable (F k))
    (hFfin : ∀ k, k ≤ q → (F k '' S).Finite)
    (hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S,
      F b x = F b y → F a x = F a y)
    (hZm : Measurable Z)
    (hZcard : ∀ x ∈ S,
      (Z '' {y | y ∈ S ∧ F z y = F z x}).Finite ∧
      (Z '' {y | y ∈ S ∧ F z y = F z x}).ncard ≤ M)
    (A : Finset ℕ) (hA : ∀ k ∈ A, k < q ∧ z ≤ k ∧ k + C ≤ q)
    (N τ α : ℝ) (hN : 1 ≤ N) (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    ((A.filter (fun k => ENNReal.ofReal α < badMass μ S F Z C k (N ^ τ))).card : ℝ) *
      (τ * Real.log N * α) ≤ (C : ℝ) * Real.log (M : ℝ) + (q : ℝ) := by
  classical
  have hSne : S.Nonempty := nonempty_of_measure_ne_zero (by
    have hmass : μ S = 1 := by
      simpa [hμS] using measure_add_measure_compl (μ := μ) hS
    rw [hmass]
    exact one_ne_zero)
  have hZfin : (Z '' S).Finite := finite_palette_range S (F z) Z (hFfin z hzq)
    (fun x hx => (hZcard x hx).1)
  obtain ⟨n, hn, X, G, W, hX, hGX, hWX, hrepr⟩ := exists_joint_record_code S hS hSne
    (fun v : Fin (q + 1) => F v.val) Z
    (fun v => hFm v.val (by omega)) hZm
    (fun v => hFfin v.val (by omega)) hZfin
  let G' : ℕ → Fin n → ℕ := fun a => G ⟨min (z + a) q, by omega⟩
  have hG' (a : ℕ) (x : Ω) (hx : x ∈ S) :
      G' a (X x) = F (min (z + a) q) x := hGX x hx _
  have hGnest : ∀ a i j, G' (a + 1) i = G' (a + 1) j → G' a i = G' a j := by
    intro a i j hij
    obtain ⟨x, hx, hix, hWi⟩ := hrepr i
    obtain ⟨y, hy, hjy, hWj⟩ := hrepr j
    change G _ i = G _ j at hij ⊢
    simp only [hix, hjy] at hij ⊢
    exact hnest _ _ (by omega) (by omega) x hx y hy hij
  have hGcard : ∀ i,
      ((Finset.univ.filter (fun j => 0 < atomMass μ X j ∧ G' 0 j = G' 0 i)).image W).card ≤ M := by
    intro i
    obtain ⟨x, hx, hix, hWi⟩ := hrepr i
    have hsub :
        (↑((Finset.univ.filter (fun j => 0 < atomMass μ X j ∧ G' 0 j = G' 0 i)).image W) : Set ℕ) ⊆
          Z '' {y | y ∈ S ∧ F z y = F z x} := by
      intro b hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨y, hy, hjy, hWj⟩ := hrepr j
      refine ⟨y, ⟨hy, ?_⟩, hWj.symm⟩
      have hij := (Finset.mem_filter.mp hj).2.2
      change G _ j = G _ i at hij
      simp only [hjy, hix, Nat.add_zero, Nat.min_eq_left hzq] at hij
      exact hij
    have hc := Set.ncard_le_ncard hsub (hZcard x hx).1
    have hc' : ((Finset.univ.filter (fun j =>
        0 < atomMass μ X j ∧ G' 0 j = G' 0 i)).image W).card ≤
          (Z '' {y | y ∈ S ∧ F z y = F z x}).ncard := by simpa only [Set.ncard_coe_finset] using hc
    exact hc'.trans (hZcard x hx).2
  let B := A.filter (fun k => ENNReal.ofReal α < badMass μ S F Z C k (N ^ τ))
  let B' := (Finset.range q).filter (fun a =>
    α < likelihoodFailureMass (atomMass μ X) G' W C a (N ^ τ))
  have hB : ∀ k ∈ B, k - z ∈ B' := by
    intro k hk
    obtain ⟨hkA, hkbad⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkq, hzk, hkC⟩ := hA k hkA
    have heq : (badMass μ S F Z C k (N ^ τ)).toReal =
        likelihoodFailureMass (atomMass μ X) G' W C (k - z) (N ^ τ) := by
      apply badMass_eq_failureMass μ S hμS F Z X hX G' W k (k - z) C (N ^ τ)
      · intro x hx
        have he : min (z + (k - z)) q = k := by omega
        simpa only [he] using hG' (k - z) x hx
      · intro x hx
        have he : min (z + (k - z + C)) q = k + C := by omega
        simpa only [he] using hG' (k - z + C) x hx
      · exact hWX
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [← heq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hα (measure_ne_top μ _)).mp hkbad
  have hBinj : (↑B : Set ℕ).InjOn (fun k => k - z) := by
    intro k hk l hl he
    have hkz := (hA k (Finset.mem_filter.mp hk).1).2.1
    have hlz := (hA l (Finset.mem_filter.mp hl).1).2.1
    change k - z = l - z at he
    omega
  have hcard : (B.card : ℝ) ≤ B'.card := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun k => k - z) hB hBinj
  calc
    _ ≤ (B'.card : ℝ) * (τ * Real.log N * α) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hτ (Real.log_nonneg hN)) hα)
    _ ≤ _ := palette_bad_steps_bound hpal n q C M (atomMass μ X) G' W hC hM
      (atomMass_nonneg μ X) (sum_atomMass_eq_one μ X hX) hGnest hGcard N τ α hN hτ hα

theorem badMass_comp {Ω Ζ Ζ' : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (e : Ζ → Ζ') (he : Function.Injective e) (C k : ℕ) (R : ℝ) :
    badMass μ S F (e ∘ Z) C k R = badMass μ S F Z C k R := by
  simp only [badMass, supportLikelihood_comp μ S F Z e he]

/-- Integer-pair palettes can be encoded without changing any bad event. -/
theorem continuous_pair_bad_steps_bound (hpal : PaletteEstimate)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (Z : Ω → ℤ × ℤ) (q z C M : ℕ)
    (hzq : z ≤ q) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hFm : ∀ k, k ≤ q → Measurable (F k))
    (hFfin : ∀ k, k ≤ q → (F k '' S).Finite)
    (hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S,
      F b x = F b y → F a x = F a y)
    (hZm : Measurable Z)
    (hZcard : ∀ x ∈ S,
      (Z '' {y | y ∈ S ∧ F z y = F z x}).Finite ∧
      (Z '' {y | y ∈ S ∧ F z y = F z x}).ncard ≤ M)
    (A : Finset ℕ) (hA : ∀ k ∈ A, k < q ∧ z ≤ k ∧ k + C ≤ q)
    (N τ α : ℝ) (hN : 1 ≤ N) (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    ((A.filter (fun k => ENNReal.ofReal α < badMass μ S F Z C k (N ^ τ))).card : ℝ) *
      (τ * Real.log N * α) ≤ (C : ℝ) * Real.log (M : ℝ) + (q : ℝ) := by
  classical
  let e : ℤ × ℤ → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  have hcard : ∀ x ∈ S,
      ((e ∘ Z) '' {y | y ∈ S ∧ F z y = F z x}).Finite ∧
      ((e ∘ Z) '' {y | y ∈ S ∧ F z y = F z x}).ncard ≤ M := by
    intro x hx
    rw [Set.image_comp]
    exact ⟨(hZcard x hx).1.image e,
      (Set.ncard_image_le (hZcard x hx).1).trans (hZcard x hx).2⟩
  have hb := continuous_bad_steps_bound hpal μ S hS hμS F (e ∘ Z) q z C M hzq hC hM
    hFm hFfin hnest ((measurable_of_countable e).comp hZm) hcard A hA N τ α hN hτ hα
  simpa only [badMass_comp μ S F Z e he] using hb

end Submission.Obl.k4_matching_cofinal_palette_selection
