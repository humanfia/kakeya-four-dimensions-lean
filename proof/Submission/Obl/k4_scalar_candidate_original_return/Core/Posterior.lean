import Mathlib

/-!
# Posterior-maximizing neighbour lists

Finitely many disjoint covered sets `C m` carry labels `bin m`.  Observing only a record
`rec p` (countably many values), choose for each record the label `bstar O` maximizing the
covered mass of its neighbourhood.  Then the listed success loses at most the mass of the
non-neighbour pairs of the conditional pair law on records.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.Posterior

open MeasureTheory Set

variable {α Q β : Type*} [MeasurableSpace α] [Countable Q]

/-- The mass of non-neighbour pairs of the conditional pair law on records. -/
noncomputable def badPairMass (μ : Measure α) {n : ℕ} (C : Fin n → Set α) (rec : α → Q)
    (bin : Fin n → β) (nbr : β → β → Prop) : ENNReal :=
  by
    classical
    exact ∑' O, ∑ m, ∑ m', if nbr (bin m) (bin m') then 0 else
      μ (C m ∩ rec ⁻¹' {O}) * μ (C m' ∩ rec ⁻¹' {O}) / μ ((⋃ m'', C m'') ∩ rec ⁻¹' {O})

/-- The cells `C m ∩ rec⁻¹{O}` selected by a predicate partition the corresponding union,
so its mass is the sum over records of the selected cell masses. -/
theorem measure_cells (μ : Measure α) {n : ℕ} (C : Fin n → Set α)
    (hC : ∀ m, MeasurableSet (C m))
    (hdisj : Pairwise (fun m m' => Disjoint (C m) (C m')))
    (rec : α → Q) (hrec : ∀ O, MeasurableSet (rec ⁻¹' {O}))
    (T : Q → Fin n → Prop) [∀ O m, Decidable (T O m)] :
    μ (⋃ m, C m ∩ rec ⁻¹' {O | T O m}) =
      ∑' O, ∑ m, if T O m then μ (C m ∩ rec ⁻¹' {O}) else 0 := by
  let D : Q × Fin n → Set α := fun p => if T p.1 p.2 then C p.2 ∩ rec ⁻¹' {p.1} else ∅
  have hsub : ∀ q, D q ⊆ C q.2 ∩ rec ⁻¹' {q.1} := by
    intro q
    by_cases h : T q.1 q.2
    · simp only [D, h, ite_true]
      exact le_rfl
    · simp only [D, h, ite_false]
      exact Set.empty_subset _
  have hD : ∀ p, MeasurableSet (D p) := by
    intro p
    by_cases h : T p.1 p.2
    · simp only [D, h, ite_true]
      exact (hC p.2).inter (hrec p.1)
    · simp only [D, h, ite_false]
      exact MeasurableSet.empty
  have hDdisj : Pairwise (Function.onFun Disjoint D) := by
    intro p p' hpp'
    refine Disjoint.mono (hsub p) (hsub p') ?_
    rcases p with ⟨O, m⟩
    rcases p' with ⟨O', m'⟩
    by_cases hm : m = m'
    · subst hm
      have hO : O ≠ O' := fun h => hpp' (by rw [h])
      rw [Set.disjoint_left]
      rintro x ⟨_, hx⟩ ⟨_, hx'⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
      exact hO (hx.symm.trans hx')
    · exact (hdisj hm).mono Set.inter_subset_left Set.inter_subset_left
  have hU : (⋃ m, C m ∩ rec ⁻¹' {O | T O m}) = ⋃ p, D p := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hxm, hT⟩
      refine ⟨(rec x, m), ?_⟩
      simp only [D, hT, ite_true]
      exact ⟨hxm, rfl⟩
    · rintro ⟨⟨O, m⟩, hx⟩
      by_cases h : T O m
      · simp only [D, h, ite_true] at hx
        obtain ⟨hxm, hxO⟩ := hx
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxO
        exact ⟨m, hxm, hxO ▸ h⟩
      · simp only [D, h, ite_false] at hx
        exact hx.elim
  rw [hU, measure_iUnion hDdisj hD, ENNReal.tsum_prod']
  congr 1
  ext O
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : T O m
  · simp [D, h]
  · simp [D, h]

/-- The per-record inequality: the record's covered mass is at most the mass listed by a
maximizing neighbourhood plus the non-neighbour part of the record's pair law. -/
theorem record_bound {n : ℕ} (a : Fin n → ENNReal) (ha : ∀ m, a m ≠ ⊤)
    (bin : Fin n → β) (nbr : β → β → Prop) [DecidableRel nbr] (b : β)
    (hb : ∀ m, (∑ m', if nbr (bin m) (bin m') then a m' else 0) ≤
      ∑ m', if nbr b (bin m') then a m' else 0) :
    (∑ m, a m) ≤ (∑ m, if nbr b (bin m) then a m else 0) +
      ∑ m, ∑ m', if nbr (bin m) (bin m') then 0 else a m * a m' / ∑ m'', a m'' := by
  set t := ∑ m, a m with ht
  by_cases h0 : t = 0
  · rw [h0]
    exact zero_le
  have htop : t ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun m _ => ha m)
  -- the full pair law of the record has mass `t`
  have hfull : (∑ m, ∑ m', a m * a m' / t) = t := by
    have h1 : (∑ m, ∑ m', a m * a m' / t) = t⁻¹ * ((∑ m, a m) * ∑ m', a m') := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m' _
      rw [ENNReal.div_eq_inv_mul]
    rw [h1, ← ht, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  -- split the pair law into neighbour and non-neighbour pairs
  have hsplit : (∑ m, ∑ m', a m * a m' / t) =
      (∑ m, ∑ m', if nbr (bin m) (bin m') then a m * a m' / t else 0) +
        ∑ m, ∑ m', if nbr (bin m) (bin m') then 0 else a m * a m' / t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m' _
    split_ifs <;> simp
  -- the neighbour part is at most the maximal listed mass
  have hnbr : (∑ m, ∑ m', if nbr (bin m) (bin m') then a m * a m' / t else 0) ≤
      ∑ m, if nbr b (bin m) then a m else 0 := by
    have hrow : ∀ m, (∑ m', if nbr (bin m) (bin m') then a m * a m' / t else 0) =
        (a m / t) * ∑ m', if nbr (bin m) (bin m') then a m' else 0 := by
      intro m
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m' _
      split_ifs
      · rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
      · simp
    calc (∑ m, ∑ m', if nbr (bin m) (bin m') then a m * a m' / t else 0)
        = ∑ m, (a m / t) * ∑ m', if nbr (bin m) (bin m') then a m' else 0 :=
          Finset.sum_congr rfl (fun m _ => hrow m)
      _ ≤ ∑ m, (a m / t) * ∑ m', if nbr b (bin m') then a m' else 0 :=
          Finset.sum_le_sum (fun m _ => mul_le_mul' le_rfl (hb m))
      _ = (∑ m, a m / t) * ∑ m', if nbr b (bin m') then a m' else 0 := by
          rw [Finset.sum_mul]
      _ = ∑ m', if nbr b (bin m') then a m' else 0 := by
          have hdiv : (∑ m, a m / t) = t / t := by
            simp_rw [ENNReal.div_eq_inv_mul]
            rw [← Finset.mul_sum, ← ht]
          rw [hdiv, ENNReal.div_self h0 htop, one_mul]
  calc t = (∑ m, ∑ m', a m * a m' / t) := hfull.symm
    _ = _ := hsplit
    _ ≤ _ := add_le_add hnbr le_rfl

theorem posterior_success [Inhabited β] (μ : Measure α) [IsFiniteMeasure μ] {n : ℕ}
    (C : Fin n → Set α) (hC : ∀ m, MeasurableSet (C m))
    (hdisj : Pairwise (fun m m' => Disjoint (C m) (C m')))
    (rec : α → Q) (hrec : ∀ O, MeasurableSet (rec ⁻¹' {O}))
    (bin : Fin n → β) (nbr : β → β → Prop) :
    ∃ bstar : Q → β,
      μ (⋃ m, C m) ≤ μ (⋃ m, C m ∩ rec ⁻¹' {O | nbr (bstar O) (bin m)}) +
        badPairMass μ C rec bin nbr := by
  classical
  let f : Q → β → ENNReal := fun O b =>
    ∑ m', if nbr b (bin m') then μ (C m' ∩ rec ⁻¹' {O}) else 0
  have hkey : ∀ O, ∃ b : β, ∀ m, f O (bin m) ≤ f O b := by
    intro O
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨default, fun m => m.elim0⟩
    · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨m₀, -, hm₀⟩ :=
        Finset.exists_max_image Finset.univ (fun m => f O (bin m)) Finset.univ_nonempty
      exact ⟨bin m₀, fun m => hm₀ m (Finset.mem_univ m)⟩
  choose bstar hbstar using hkey
  refine ⟨bstar, ?_⟩
  have htot : ∀ O, μ ((⋃ m'', C m'') ∩ rec ⁻¹' {O}) = ∑ m, μ (C m ∩ rec ⁻¹' {O}) := by
    intro O
    rw [Set.iUnion_inter, measure_iUnion _ (fun m => (hC m).inter (hrec O)), tsum_fintype]
    intro m m' hmm'
    exact (hdisj hmm').mono Set.inter_subset_left Set.inter_subset_left
  have hA : μ (⋃ m, C m) = ∑' O, ∑ m, μ (C m ∩ rec ⁻¹' {O}) := by
    have h := measure_cells μ C hC hdisj rec hrec (fun _ _ => True)
    simp only [Set.ofPred_true, Set.preimage_univ, Set.inter_univ, ite_true] at h
    exact h
  have hB : μ (⋃ m, C m ∩ rec ⁻¹' {O | nbr (bstar O) (bin m)}) =
      ∑' O, ∑ m, if nbr (bstar O) (bin m) then μ (C m ∩ rec ⁻¹' {O}) else 0 :=
    measure_cells μ C hC hdisj rec hrec (fun O m => nbr (bstar O) (bin m))
  rw [hA, hB, badPairMass]
  simp_rw [htot]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro O
  exact record_bound (fun m => μ (C m ∩ rec ⁻¹' {O})) (fun m => measure_ne_top _ _)
    bin nbr (bstar O) (hbstar O)

end Submission.Obl.k4_scalar_candidate_original_return.Posterior
