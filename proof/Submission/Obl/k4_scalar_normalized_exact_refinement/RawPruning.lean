import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass
import Submission.Obl.k4_scalar_normalized_exact_refinement.RawNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

/-- A polynomial prior-mass cutoff preserves subpower selected mass. The
remaining charts are indexed by a finite initial segment without duplication. -/
lemma finite_prior_pruning {X Γ : Type*} [MeasurableSpace X] [Fintype Γ]
    {n : ℕ} (ν : Γ → Measure X) (μ : Γ → Measure (X × ℝ)) (w : Γ → ENNReal)
    (γ : Fin n → Γ) (A : Fin n → Set X) (C : Fin n → Set (X × ℝ))
    (t₀ : Fin n → ℝ) (dt N ε B : ℝ)
    (hN : 2 ≤ N) (hε : ε ≤ 1) (hNε : 2 ≤ N ^ ε)
    (hn : (n : ℝ) ≤ N ^ B)
    (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hμ : ∀ g, μ g ≤ (ν g).prod volume) (hw : ∀ g, w g ≤ 1) (hdt : dt ≤ 1)
    (hC : ∀ i, C i ⊆ A i ×ˢ Icc (t₀ i) (t₀ i + dt))
    (hmass : ENNReal.ofReal (N ^ (-ε)) ≤
      ∑ g, w g * μ g {q | ∃ i, γ i = g ∧ q ∈ C i}) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin n),
      (∀ i, N ^ (-(B + 2)) ≤ (ν (γ (e i)) (A (e i))).toReal) ∧
      ENNReal.ofReal (N ^ (-2 * ε)) ≤
        ∑ g, w g * μ g {q | ∃ i : Fin m, γ (e i) = g ∧ q ∈ C (e i)} := by
  classical
  let τ := ENNReal.ofReal (N ^ (-(B + 2)))
  let good : Finset (Fin n) := Finset.univ.filter (fun i => τ ≤ ν (γ i) (A i))
  let bad : Finset (Fin n) := Finset.univ \ good
  let retained : Γ → Set (X × ℝ) := fun g => {q | ∃ i, γ i = g ∧ i ∈ good ∧ q ∈ C i}
  let deleted : Γ → Set (X × ℝ) := fun g => {q | ∃ i, γ i = g ∧ i ∈ bad ∧ q ∈ C i}
  have hsmall i (hi : i ∈ bad) : ν (γ i) (A i) ≤ τ := by
    have hnot := (Finset.mem_sdiff.mp hi).2
    exact (not_le.mp (fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))).le
  have hdeleted : (∑ g, w g * μ g (deleted g)) ≤ ENNReal.ofReal (N ^ (-2 : ℝ)) := by
    have hd := deleted_small_assignments_mass_le ν μ w γ A C t₀ dt bad τ hμ hw hdt hC hsmall
    change (∑ g, w g * μ g (deleted g)) ≤ _ at hd
    apply hd.trans
    have hN0 : 0 < N := by linarith
    calc
      (Fintype.card (Fin n) : ENNReal) * τ = ENNReal.ofReal ((n : ℝ) * N ^ (-(B + 2))) := by
        simp only [Fintype.card_fin, τ, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      _ ≤ ENNReal.ofReal (N ^ B * N ^ (-(B + 2))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hN0.le _))
      _ = ENNReal.ofReal (N ^ (-2 : ℝ)) := by
        rw [← Real.rpow_add hN0]
        congr 2
        ring
  have hcover : (∑ g, w g * μ g {q | ∃ i, γ i = g ∧ q ∈ C i}) ≤
      (∑ g, w g * μ g (retained g)) + ∑ g, w g * μ g (deleted g) := by
    apply k4_quadratic_atlas_normalization.weighted_mass_le_retained_add_deleted
    intro g q hq
    obtain ⟨i, hγ, hi⟩ := hq
    by_cases hg : i ∈ good
    · exact Or.inl ⟨i, hγ, hg, hi⟩
    · exact Or.inr ⟨i, hγ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hg⟩, hi⟩
  have hretained := retain_power_mass_after_prior_cut hN hε hNε _ _ _ hmass hcover hdeleted
  let e₀ := (Fintype.equivFin {i // i ∈ good}).symm
  let e : Fin (Fintype.card {i // i ∈ good}) ↪ Fin n :=
    ⟨fun i => (e₀ i).1, fun _ _ he => e₀.injective (Subtype.ext he)⟩
  refine ⟨_, e, ?_, ?_⟩
  · intro i
    have hi := (Finset.mem_filter.mp (e₀ i).2).2
    let : IsProbabilityMeasure (ν (γ (e i))) := hprob (γ (e i))
    have hfin : ν (γ (e i)) (A (e i)) ≠ ∞ := measure_ne_top _ _
    have hreal := ENNReal.toReal_mono hfin hi
    simpa only [τ, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (show 0 ≤ N by linarith) (-(B + 2)))] using hreal
  · have heq g : retained g = {q | ∃ i : Fin (Fintype.card {i // i ∈ good}),
        γ (e i) = g ∧ q ∈ C (e i)} := by
      ext q
      constructor
      · rintro ⟨i, hγ, hi, hq⟩
        obtain ⟨i', hi'⟩ := e₀.surjective ⟨i, hi⟩
        have heval : e i' = i := congrArg Subtype.val hi'
        exact ⟨i', by simpa only [heval] using hγ, by simpa only [heval] using hq⟩
      · rintro ⟨i, hγ, hq⟩
        exact ⟨e i, hγ, (e₀ i).2, hq⟩
    simpa only [heq] using hretained

end Submission.Obl.k4_scalar_normalized_exact_refinement
