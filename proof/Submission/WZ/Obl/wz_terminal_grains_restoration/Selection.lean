-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

/-!
# Dyadic selection of coarse fibres and of a common multiplicity class

Starting from a fine family `S'` with shadings `Z'` assigned to coarse tubes by `f`, keep the
whole fibres whose cardinalities lie in one dyadic class, and then, inside every kept fibre,
the points whose multiplicity lies in one common dyadic class. Each step loses at most a
factor `Nat.log 2 n + 1` of the shading mass.
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory Finset

noncomputable section

/-- The cardinality of the fibre of `k` in `S`. -/
def fc {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (k : Fin N) : ℕ :=
  (S.filter (fun i => f i = k)).card

theorem fc_le {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (k : Fin N) : fc S f k ≤ n := by
  unfold fc
  calc (S.filter (fun i => f i = k)).card ≤ S.card := card_filter_le _ _
    _ ≤ (univ : Finset (Fin n)).card := card_le_univ _
    _ = n := by simp

/-- Pigeonholing a sum over the classes `0, …, Λ`. -/
theorem pigeon_sum (Λ : ℕ) (F : ℕ → ENNReal) :
    ∃ ℓ ≤ Λ, ∑ ℓ' ∈ range (Λ + 1), F ℓ' ≤ ((Λ + 1 : ℕ) : ENNReal) * F ℓ := by
  obtain ⟨ℓ, hℓ, hmax⟩ := (range (Λ + 1)).exists_max_image F ⟨0, by simp⟩
  refine ⟨ℓ, Nat.lt_succ_iff.1 (mem_range.1 hℓ), ?_⟩
  calc ∑ ℓ' ∈ range (Λ + 1), F ℓ' ≤ (range (Λ + 1)).card • F ℓ := sum_le_card_nsmul _ _ _ hmax
    _ = ((Λ + 1 : ℕ) : ENNReal) * F ℓ := by rw [card_range, nsmul_eq_mul]

theorem select {α : Type*} [MeasurableSpace α] (μ : Measure α) {n N : ℕ} (S' : Finset (Fin n))
    (f : Fin n → Fin N) (Z' : Fin n → Set α) (hZ' : ∀ i, MeasurableSet (Z' i)) :
    ∃ (R : Finset (Fin N)) (S₁ : Finset (Fin n)) (E : Fin N → Set α) (ℓ : ℕ),
      S₁ ⊆ S' ∧ (∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R)) ∧ (∀ k ∈ R, ∃ i ∈ S₁, f i = k) ∧
      (∀ k ∈ R, ∀ k' ∈ R, fc S' f k ≤ 2 * fc S' f k') ∧
      (∀ k, MeasurableSet (E k)) ∧
      (∀ k p, p ∈ E k → (∃ i ∈ S₁, f i = k ∧ p ∈ Z' i) →
        2 ^ ℓ ≤ mult (S₁.filter (fun i => f i = k)) Z' p ∧
          mult (S₁.filter (fun i => f i = k)) Z' p < 2 ^ (ℓ + 1)) ∧
      ∑ i ∈ S', μ (Z' i) ≤
        (((Nat.log 2 n + 1) ^ 2 : ℕ) : ENNReal) * ∑ i ∈ S₁, μ (Z' i ∩ E (f i)) := by
  classical
  set Λ := Nat.log 2 n with hΛ
  -- fibre classes
  set cls₁ : Fin n → ℕ := fun i => Nat.log 2 (fc S' f (f i)) with hcls₁
  have hcls₁Λ : ∀ i ∈ S', cls₁ i ≤ Λ := fun i _ => Nat.log_mono_right (fc_le S' f (f i))
  obtain ⟨ℓ₁, -, h1⟩ := pigeon S' cls₁ Λ hcls₁Λ (fun i => μ (Z' i))
  set S₁ := S'.filter (fun i => cls₁ i = ℓ₁) with hS₁
  set R := S₁.image f with hR
  have hS₁S' : S₁ ⊆ S' := filter_subset _ _
  have hmemR : ∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R) := by
    intro i hi
    constructor
    · intro h; exact mem_image.2 ⟨i, h, rfl⟩
    · intro h
      obtain ⟨i', hi', hfi'⟩ := mem_image.1 h
      have h2 := (mem_filter.1 hi').2
      refine mem_filter.2 ⟨hi, ?_⟩
      simp only [hcls₁] at h2 ⊢
      rw [← hfi']; exact h2
  have hRS : ∀ k ∈ R, ∃ i ∈ S₁, f i = k := fun k hk => mem_image.1 hk
  have hRcls : ∀ k ∈ R, 2 ^ ℓ₁ ≤ fc S' f k ∧ fc S' f k < 2 ^ (ℓ₁ + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := hRS k hk
    have hcl : Nat.log 2 (fc S' f (f i)) = ℓ₁ := (mem_filter.1 hi).2
    have hpos : fc S' f (f i) ≠ 0 := by
      unfold fc
      apply Nat.pos_iff_ne_zero.1
      apply card_pos.2
      exact ⟨i, mem_filter.2 ⟨hS₁S' hi, rfl⟩⟩
    refine ⟨?_, ?_⟩
    · rw [← hcl]; exact Nat.pow_log_le_self 2 hpos
    · rw [← hcl]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hbal : ∀ k ∈ R, ∀ k' ∈ R, fc S' f k ≤ 2 * fc S' f k' := by
    intro k hk k' hk'
    have h1 := (hRcls k hk).2
    have h2 := (hRcls k' hk').1
    rw [pow_succ] at h1
    omega
  -- multiplicity classes
  set cls₂ : Fin N → α → ℕ := fun k p => Nat.log 2 (mult (S₁.filter (fun i => f i = k)) Z' p)
    with hcls₂
  have hcls₂meas : ∀ k, Measurable (cls₂ k) := by
    intro k
    have hm := measurable_mult (S₁.filter (fun i => f i = k)) Z' (fun i _ => hZ' i)
    exact (measurable_from_nat (f := fun m : ℕ => Nat.log 2 m)).comp hm
  set E' : ℕ → Fin N → Set α := fun ℓ k => cls₂ k ⁻¹' {ℓ} with hE'
  have hE'meas : ∀ ℓ k, MeasurableSet (E' ℓ k) := fun ℓ k =>
    hcls₂meas k (measurableSet_singleton ℓ)
  have hsplit : ∀ i ∈ S₁, μ (Z' i) = ∑ ℓ ∈ range (Λ + 1), μ (Z' i ∩ E' ℓ (f i)) := by
    intro i _
    refine measure_eq_sum_classes μ (hZ' i) (cls₂ (f i)) (hcls₂meas (f i)) Λ ?_
    intro p _
    have : mult (S₁.filter (fun i' => f i' = f i)) Z' p ≤ n := by
      refine (mult_le_card _ _ _).trans ?_
      calc (S₁.filter (fun i' => f i' = f i)).card ≤ (univ : Finset (Fin n)).card :=
            card_le_univ _
        _ = n := by simp
    exact Nat.log_mono_right this
  have h2sum : ∑ i ∈ S₁, μ (Z' i) =
      ∑ ℓ ∈ range (Λ + 1), ∑ i ∈ S₁, μ (Z' i ∩ E' ℓ (f i)) := by
    rw [sum_congr rfl hsplit, sum_comm]
  obtain ⟨ℓ₂, -, h2⟩ := pigeon_sum Λ (fun ℓ => ∑ i ∈ S₁, μ (Z' i ∩ E' ℓ (f i)))
  refine ⟨R, S₁, E' ℓ₂, ℓ₂, hS₁S', hmemR, hRS, hbal, hE'meas ℓ₂, ?_, ?_⟩
  · intro k p hp ⟨i, hi, hfi, hpi⟩
    have hcl : Nat.log 2 (mult (S₁.filter (fun i => f i = k)) Z' p) = ℓ₂ := hp
    have hpos : mult (S₁.filter (fun i => f i = k)) Z' p ≠ 0 :=
      (mult_pos_of_mem (mem_filter.2 ⟨hi, hfi⟩) hpi).ne'
    refine ⟨?_, ?_⟩
    · rw [← hcl]; exact Nat.pow_log_le_self 2 hpos
    · rw [← hcl]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  · calc ∑ i ∈ S', μ (Z' i) ≤ ((Λ + 1 : ℕ) : ENNReal) * ∑ i ∈ S₁, μ (Z' i) := h1
      _ = ((Λ + 1 : ℕ) : ENNReal) * ∑ ℓ ∈ range (Λ + 1), ∑ i ∈ S₁, μ (Z' i ∩ E' ℓ (f i)) := by
          rw [h2sum]
      _ ≤ ((Λ + 1 : ℕ) : ENNReal) * (((Λ + 1 : ℕ) : ENNReal) *
            ∑ i ∈ S₁, μ (Z' i ∩ E' ℓ₂ (f i))) := by gcongr
      _ = (((Λ + 1) ^ 2 : ℕ) : ENNReal) * ∑ i ∈ S₁, μ (Z' i ∩ E' ℓ₂ (f i)) := by
          push_cast; ring

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
