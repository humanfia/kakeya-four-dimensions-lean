import Submission.Obl.k4_scalar_noisy_block_packets.Interface

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter
open scoped ENNReal

/-- A finite union has a member carrying at least its average mass. -/
theorem exists_mass_ge_average {α : Type*} [MeasurableSpace α] {b : ℕ}
    (hb : 0 < b) (μ : Measure α) (S : Fin b → Set α) :
    ∃ j : Fin b, μ (⋃ i, S i) / b ≤ μ (S j) := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => μ (S i))
    Finset.univ_nonempty
  refine ⟨j, (ENNReal.div_le_iff (by simpa using hb.ne') (by simp)).2 ?_⟩
  calc
    μ (⋃ i, S i) ≤ ∑ i, μ (S i) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _i : Fin b, μ (S j) := Finset.sum_le_sum fun i _ => hj i (Finset.mem_univ _)
    _ = μ (S j) * b := by simp [nsmul_eq_mul, mul_comm]

noncomputable def blockLeft (T : ℕ) (j : Fin (2 ^ T)) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ T

noncomputable def blockLength (T : ℕ) : ℝ := ((2 : ℝ) ^ T)⁻¹

noncomputable def blockInterval (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (blockLeft T j) (blockLeft T j + blockLength T)

lemma blockInterval_eq (T : ℕ) (j : Fin (2 ^ T)) :
    blockInterval T j = Icc ((j : ℝ) / (2 : ℝ) ^ T)
      (((j : ℝ) + 1) / (2 : ℝ) ^ T) := by
  simp only [blockInterval, blockLeft, blockLength, add_div, one_div]

lemma blockLeft_nonneg (T : ℕ) (j : Fin (2 ^ T)) : 0 ≤ blockLeft T j := by
  exact div_nonneg (by positivity) (by positivity)

lemma blockRight_le_one (T : ℕ) (j : Fin (2 ^ T)) :
    blockLeft T j + blockLength T ≤ 1 := by
  rw [blockLeft, blockLength, ← one_div, ← add_div, div_le_one (by positivity)]
  have hj : (j : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    exact_mod_cast j.isLt
  exact hj

/-- Fixing one time block and enumerating its labels preserves every pointwise property,
while losing at most the number of blocks in total selected mass. -/
theorem common_block {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (T n : ℕ) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α) :
    ∃ (j₀ : Fin (2 ^ T)) (n' : ℕ) (e : Fin n' → Fin n),
      Function.Injective e ∧ (∀ i, j (e i) = j₀) ∧
      (∀ i, j i = j₀ → ∃ i', e i' = i) ∧
      μ {p | ∃ i, p.1 ∈ A i ∧ p.2 ∈ blockInterval T (j i)} / (2 ^ T : ℕ) ≤
        μ {p | (∃ i, p.1 ∈ A (e i)) ∧ p.2 ∈ blockInterval T j₀} := by
  classical
  let S : Fin (2 ^ T) → Set (α × ℝ) := fun b =>
    {p | ∃ i, j i = b ∧ p.1 ∈ A i ∧ p.2 ∈ blockInterval T b}
  obtain ⟨j₀, hj₀⟩ := exists_mass_ge_average (by positivity) μ S
  let B := {i : Fin n // j i = j₀}
  let e₀ : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  refine ⟨j₀, Fintype.card B, fun i => (e₀ i).val, ?_, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp e₀.injective
  · exact fun i => (e₀ i).property
  · intro i hi
    exact ⟨e₀.symm ⟨i, hi⟩, congrArg Subtype.val (e₀.apply_symm_apply _)⟩
  · have hU : (⋃ b, S b) = {p | ∃ i, p.1 ∈ A i ∧ p.2 ∈ blockInterval T (j i)} := by
      ext p
      simp only [mem_iUnion, S, mem_ofPred_eq]
      constructor
      · rintro ⟨b, i, hib, hi, ht⟩
        exact ⟨i, hi, hib ▸ ht⟩
      · rintro ⟨i, hi, ht⟩
        exact ⟨j i, i, rfl, hi, ht⟩
    have hS : S j₀ = {p | (∃ i, p.1 ∈ A (e₀ i).val) ∧
        p.2 ∈ blockInterval T j₀} := by
      ext p
      constructor
      · rintro ⟨i, hi, hA, ht⟩
        refine ⟨⟨e₀.symm ⟨i, hi⟩, ?_⟩, ht⟩
        simpa using hA
      · rintro ⟨⟨i, hA⟩, ht⟩
        exact ⟨(e₀ i).val, (e₀ i).property, hA, ht⟩
    rwa [hU, hS] at hj₀

/-- Convert packets with common width and blockwise disjoint assignments into the frozen
noisy output. All floors refer to the original, unnormalized incidence law. -/
theorem noisyOutput_of_blocks (N d s m c ε β : ℝ) (angular : Bool) (μ : Measure Inc)
    (T n : ℕ) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set Line)
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (hq : N ^ (-ε) ≤ blockLength T)
    (hβlo : N ^ (-m) / N ^ ε ≤ β) (hβhi : β ≤ N ^ ε)
    (hangular : angular = true → N ^ (-ε) ≤ β)
    (hA : ∀ i, MeasurableSet (A i))
    (hdis : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hgeo : ∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧
      (∀ t ∈ blockInterval T (j i), ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧
      (∀ l ∈ A i, ∀ t ∈ blockInterval T (j i),
        |y l t - u i - t * v i| ≤ N ^ ε * β ∧
        |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)))
    (hfloor : ∀ i,
      ENNReal.ofReal (blockLength T * c * (N ^ (-s)) ^ d * β / N ^ ε) ≤
        μ (A i ×ˢ blockInterval T (j i)))
    (hmass : ENNReal.ofReal (N ^ (-ε)) ≤
      μ {p | ∃ i, p.1 ∈ A i ∧ p.2 ∈ blockInterval T (j i)} / (2 ^ T : ℕ)) :
    NoisyOutput N d s m c ε angular μ := by
  classical
  obtain ⟨j₀, n', e, heinj, hej, _, hmass'⟩ := common_block μ T n j A
  refine ⟨n', β, blockLeft T j₀, blockLength T, A ∘ e, u ∘ e, v ∘ e, P ∘ e,
    hq, blockLeft_nonneg T j₀, blockRight_le_one T j₀, hβlo, hβhi, hangular,
    fun i => hA (e i), ?_, ?_, hmass.trans hmass'⟩
  · intro i i' hne
    exact hdis (e i) (e i') (fun h => hne (heinj h)) ((hej i).trans (hej i').symm)
  · intro i
    rcases hgeo (e i) with ⟨hc, hd, hnorm, hfit⟩
    refine ⟨hc, hd, ?_, ?_, ?_⟩
    · simpa only [hej i, blockInterval, Function.comp_apply] using hnorm
    · simpa only [hej i, blockInterval, Function.comp_apply, x, y] using hfit
    · simpa only [hej i, blockInterval, Function.comp_apply] using hfloor (e i)

end Submission.Obl.k4_scalar_noisy_block_packets
