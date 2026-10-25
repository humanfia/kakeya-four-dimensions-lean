import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Interface
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FloorFamilies
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.OldLayerBudgets

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Set
open scoped ENNReal

/-- Earlier full-time layers survive further dense restrictions after all their
original-reference floors are restored together on one final submeasure. -/
theorem restore_common_layers {α : Type} [MeasurableSpace α] {m : ℕ}
    {N : ℕ → ℝ} {d e₀ ε : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ}
    (σ : Measure (α × ℝ)) (ρ : Fin m → Measure (α × ℝ))
    (δ D a : Fin m → ℝ) (n : Fin m → ℕ)
    (A : (r : Fin m) → Fin (n r) → Set α)
    (q : (r : Fin m) → Fin (n r) → Fin 3 → ℤ)
    (h : (r : Fin m) → Fin (n r) → Fin 6 → ℝ)
    (hN : 1 ≤ N k) (ha : ∀ r, 0 ≤ a r) (hδ : ∀ r, δ r ≤ ε)
    (hσ : ∀ r, σ ≤ ρ r)
    (htime : σ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hsource : ∀ r, LayerAt N d e₀ π b k (δ r) (ρ r) (D r) (a r)
      (n r) (A r) (q r) (h r))
    (hbudget : ENNReal.ofReal (N k ^ (-ε)) +
      (∑ r, ∑ i, ENNReal.ofReal ((D r) ^ 2 * (a r) ^ d / N k ^ ε) *
        π k (Ico ((q r i 0 : ℝ) * N k ^ (-e₀))
          (((q r i 0 : ℝ) + 1) * N k ^ (-e₀)))) < σ univ) :
    ∃ (σ' : Measure (α × ℝ)) (n' : Fin m → ℕ)
      (A' : (r : Fin m) → Fin (n' r) → Set α)
      (q' : (r : Fin m) → Fin (n' r) → Fin 3 → ℤ)
      (h' : (r : Fin m) → Fin (n' r) → Fin 6 → ℝ),
      σ' ≤ σ ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ σ' univ ∧
      ∀ r, LayerAt N d e₀ π b k ε σ' (D r) (a r) (n' r) (A' r) (q' r) (h' r) := by
  classical
  let E : (r : Fin m) → Fin (n r) → Set (α × ℝ) :=
    fun r i => A r i ×ˢ Icc (0 : ℝ) 1
  let W : (r : Fin m) → Fin (n r) → ℝ≥0∞ := fun r i =>
    ENNReal.ofReal ((D r) ^ 2 * (a r) ^ d / N k ^ ε) *
      π k (Ico ((q r i 0 : ℝ) * N k ^ (-e₀))
        (((q r i 0 : ℝ) + 1) * N k ^ (-e₀)))
  have hE : ∀ r i, MeasurableSet (E r i) :=
    fun r i => ((hsource r).1 i).prod measurableSet_Icc
  have hcov : ∀ r, σ {p | ∃ i, p ∈ E r i}ᶜ = 0 := by
    intro r
    have hcov₀ : σ {p | ∃ i, p.1 ∈ A r i}ᶜ = 0 :=
      le_antisymm ((hσ r _).trans_eq (hsource r).2.2.2) bot_le
    apply ae_iff.mp
    filter_upwards [ae_iff.mpr hcov₀, ae_iff.mpr htime] with p hp ht
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, hi, ht.2⟩
  obtain ⟨σ', n', e, hdom, hmass, hfloor, hcov'⟩ :=
    exists_common_floored_families σ E hE W (ENNReal.ofReal (N k ^ (-ε))) hcov hbudget
  refine ⟨σ', n', (fun r j => A r (e r j)), (fun r j => q r (e r j)),
    (fun r j => h r (e r j)), hdom, hmass, ?_⟩
  intro r
  have hpow : N k ^ δ r ≤ N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN (hδ r)
  refine ⟨fun j => (hsource r).1 _, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hsource r).2.1 _ _ ((e r).injective.ne hij)
  · intro j
    have hj := (hsource r).2.2.1 (e r j)
    refine ⟨hj.1, ?_, ?_, (hfloor r j).2⟩
    · intro t ht p hp q hq
      exact (hj.2.1 t ht p hp q hq).trans hpow
    · intro l hl t ht
      exact (hj.2.2.1 l hl t ht).trans (mul_le_mul_of_nonneg_right hpow (ha r))
  · apply measure_mono_null (t := {p | ∃ j, p ∈ E r (e r j)}ᶜ)
    · intro p hp hcontra
      obtain ⟨j, hj⟩ := hcontra
      exact hp ⟨j, hj.1⟩
    · exact hcov' r

/-- Every restored threshold sum is bounded in the same original numerator
units as its source layer, independently of the number of labels. -/
theorem LayerAt.floor_budget {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {δ ε D a : ℝ}
    {ρ : Measure (α × ℝ)} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : LayerAt N d e₀ π b k δ ρ D a n A q h) (hN : 0 < N k) :
    (∑ i, ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
      π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
        (((q i 0 : ℝ) + 1) * N k ^ (-e₀)))) ≤
      ENNReal.ofReal (N k ^ (δ - ε)) * ρ univ := by
  have hfactor (i : Fin n) :
      ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
        π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
          (((q i 0 : ℝ) + 1) * N k ^ (-e₀))) =
      ENNReal.ofReal (N k ^ (-ε)) * (ENNReal.ofReal (D ^ 2 * a ^ d) *
        π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀))
          (((q i 0 : ℝ) + 1) * N k ^ (-e₀)))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
    congr 2
    rw [Real.rpow_neg hN.le, div_eq_mul_inv]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  calc
    _ ≤ ENNReal.ofReal (N k ^ (-ε)) * (ENNReal.ofReal (N k ^ δ) * ρ univ) :=
      mul_le_mul' le_rfl (H.numerator_budget hN)
    _ = ENNReal.ofReal (N k ^ (δ - ε)) * ρ univ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _),
        ← Real.rpow_add hN]
      congr 2
      ring

/-- A uniform source mass and small source losses control the total new floor
cost over every layer, without counting any individual assignments. -/
theorem common_layer_floor_budget {α : Type} [MeasurableSpace α] {m : ℕ}
    {N : ℕ → ℝ} {d e₀ ε δ₀ B : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ}
    (ρ : Fin m → Measure (α × ℝ)) (δ D a : Fin m → ℝ) (n : Fin m → ℕ)
    (A : (r : Fin m) → Fin (n r) → Set α)
    (q : (r : Fin m) → Fin (n r) → Fin 3 → ℤ)
    (h : (r : Fin m) → Fin (n r) → Fin 6 → ℝ)
    (hN : 1 ≤ N k) (hδ : ∀ r, δ r ≤ δ₀)
    (hB : B ≤ N k ^ δ₀) (hmass : ∀ r, ρ r univ ≤ ENNReal.ofReal B)
    (hsource : ∀ r, LayerAt N d e₀ π b k (δ r) (ρ r) (D r) (a r)
      (n r) (A r) (q r) (h r)) :
    (∑ r, ∑ i, ENNReal.ofReal ((D r) ^ 2 * (a r) ^ d / N k ^ ε) *
      π k (Ico ((q r i 0 : ℝ) * N k ^ (-e₀))
        (((q r i 0 : ℝ) + 1) * N k ^ (-e₀)))) ≤
      ENNReal.ofReal ((m : ℝ) * N k ^ (2 * δ₀ - ε)) := by
  have hNp : 0 < N k := by linarith
  have hsingle (r : Fin m) :
      (∑ i, ENNReal.ofReal ((D r) ^ 2 * (a r) ^ d / N k ^ ε) *
        π k (Ico ((q r i 0 : ℝ) * N k ^ (-e₀))
          (((q r i 0 : ℝ) + 1) * N k ^ (-e₀)))) ≤
        ENNReal.ofReal (N k ^ (2 * δ₀ - ε)) := by
    calc
      _ ≤ ENNReal.ofReal (N k ^ (δ r - ε)) * ρ r univ :=
        (hsource r).floor_budget hNp
      _ ≤ ENNReal.ofReal (N k ^ (δ₀ - ε)) * ENNReal.ofReal (N k ^ δ₀) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le hN (by linarith [hδ r])))
          ((hmass r).trans (ENNReal.ofReal_le_ofReal hB))
      _ = ENNReal.ofReal (N k ^ (2 * δ₀ - ε)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _), ← Real.rpow_add hNp]
        congr 2
        ring
  calc
    _ ≤ ∑ _r : Fin m, ENNReal.ofReal (N k ^ (2 * δ₀ - ε)) :=
      Finset.sum_le_sum (fun r _ => hsingle r)
    _ = ENNReal.ofReal ((m : ℝ) * N k ^ (2 * δ₀ - ε)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]

/-- Original domination and unit-time support bound every current mass by K. -/
theorem Hyp1.current_mass_le {α : Type} [MeasurableSpace α]
    {K : ℕ → ℝ} {ν : ℕ → Measure α} {μ ρ : ℕ → Measure (α × ℝ)}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ}
    {P : ℕ → MvPolynomial (Fin 4) ℝ} (H : Hyp1 K ν μ ρ π b P) (k : ℕ) :
    ρ k univ ≤ ENNReal.ofReal (K k) := by
  obtain ⟨-, hν, -, hμ, hρ, htime, -⟩ := H k
  letI := hν
  have heq : μ k (univ ×ˢ Icc (0 : ℝ) 1) = μ k univ := by
    have hh := measure_add_measure_compl (μ := μ k)
      (MeasurableSet.univ.prod (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)))
    simpa only [htime, add_zero] using hh
  calc
    _ ≤ μ k univ := hρ _
    _ = μ k (univ ×ˢ Icc (0 : ℝ) 1) := heq.symm
    _ ≤ (ENNReal.ofReal (K k) • ((ν k).prod volume)) (univ ×ˢ Icc (0 : ℝ) 1) := hμ _
    _ = ENNReal.ofReal (K k) := by simp

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
