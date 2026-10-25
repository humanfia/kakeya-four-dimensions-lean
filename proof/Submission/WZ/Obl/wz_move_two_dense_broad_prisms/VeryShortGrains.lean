-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.VeryShortGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.InputMass
import Submission.WZ.Obl.wz_move_two_long_grains_gain.LevelBound

/- Adapted from x0449/o152 VeryShortGrains, using accepted o174 for the count estimate. -/

/-! The high-multiplicity case has much shorter grains than the lengthening
statement explicitly assumes. This leaves room to discard fine-tube endpoints
before enlarging grains.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya

/-- The Katz--Tao multiplicity estimate gives an explicit upper bound on length. -/
theorem grain_length_sq_lt_of_fibre_count {δ h t ρ a c g : ℝ} {n N : ℕ}
    {x v : Fin n → Space} {Y Z : Fin n → Set Space} {S : Finset (Fin n)}
    {y w : Fin N → Space} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hc4 : 4 * δ ≤ c)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : H δ h n x v S Z ρ N y w f a c 0 g)
    (hhigh : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      δ ^ (-t) < (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ)) :
    c ^ 2 < 19200000 * δ ^ (t - 2 * h) := by
  obtain ⟨L, z, e, H, γ, m, hGD⟩ := wz_move_two_long_grains_gain.H_iff.mp hG
  obtain ⟨i, hiS, p, hp⟩ := cover_has_point hδ hA hC
  have hL : 0 < L := by
    have hh' : p ∈ {p | ∃ j, γ j = f i ∧ p ∈ H j} := by
      rw [hGD.2.2.2.2.2.2.1 (f i)]
      exact ⟨i, hiS, rfl, hp⟩
    obtain ⟨j, _, _⟩ := hh'
    exact Fin.pos j
  have hlevel := wz_move_two_long_grains_gain.level_le_of_katz_tao hδ hA
    (Real.rpow_nonneg hδ.le _) hC hGD hc4 hL
  have hcount := hGD.2.2.2.2.2.2.2.2.1 (f i) p ⟨i, hiS, rfl, hp⟩
  have h2m : δ ^ (-t) < 2 * m :=
    (hhigh (f i) p ⟨i, hiS, rfl, hp⟩).trans_le hcount.2
  have hc0 : 0 < c := by linarith
  have hmc : m * c ^ 2 ≤ 9600000 * δ ^ (-(2 * h)) := by
    have hcancel : δ ^ h * δ ^ (-h) = 1 := by rw [← Real.rpow_add hδ]; simp
    have hpow : δ ^ (-h) * δ ^ (-h) = δ ^ (-(2*h)) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    calc
      _ = (m * δ ^ h * c ^ 2) * δ ^ (-h) := by
        calc _ = m * c ^ 2 * (δ ^ h * δ ^ (-h)) := by rw [hcancel, mul_one]
             _ = _ := by ring
      _ ≤ (1492992 * δ ^ (-h)) * δ ^ (-h) :=
        mul_le_mul_of_nonneg_right hlevel (Real.rpow_nonneg hδ.le _)
      _ = 1492992 * δ ^ (-(2*h)) := by rw [mul_assoc, hpow]
      _ ≤ _ := by gcongr; norm_num
  have hprod : δ ^ t * δ ^ (-t) = 1 := by
    rw [← Real.rpow_add hδ]
    simp
  calc c ^ 2 = δ ^ t * (δ ^ (-t) * c ^ 2) := by rw [← mul_assoc, hprod, one_mul]
    _ < δ ^ t * (2 * m * c ^ 2) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h2m (sq_pos_of_pos hc0))
        (Real.rpow_pos_of_pos hδ _)
    _ ≤ δ ^ t * (19200000 * δ ^ (-(2 * h))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
      linarith
    _ = 19200000 * δ ^ (t - 2 * h) := by
      rw [sub_eq_add_neg, Real.rpow_add hδ]
      ring

/-- In the high-multiplicity branch of Move 2, the grain length is at most
`δ^(9ω/20)`, uniformly at sufficiently small scales. No broadness is needed. -/
theorem high_multiplicity_grains_very_short {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ h₀ d₀ : ℝ, 0 < h₀ ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → h ≤ h₀ →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
        (y w : Fin N → Space) (f : Fin n → Fin N) (a c g : ℝ),
      C δ h n x v Y S Z ρ N y w f True → H δ h n x v S Z ρ N y w f a c 0 g →
      (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
        δ ^ (-(24 * ω / 25)) < (Set.ncard {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : ℝ)) →
      c ≤ δ ^ (9 * ω / 20) := by
  let D : ℝ := (1 / 19200000 : ℝ) ^ (20 / ω)
  have hD0 : 0 < D := by dsimp [D]; positivity
  refine ⟨ω / 1000, min (1 / 100) D, by positivity, lt_min (by norm_num) hD0,
    min_le_left _ _, ?_⟩
  intro δ h hδ hδd hh n x v Y hA S Z ρ N y w f a c g hC hG hhigh
  have hδ100 : δ ≤ 1 / 100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδD : δ ≤ D := hδd.trans (min_le_right _ _)
  by_cases hc4 : 4 * δ ≤ c
  · have hc2 := grain_length_sq_lt_of_fibre_count hδ hc4 hA hC hG hhigh
    have hsmall : δ ^ (ω / 20) ≤ 1 / 19200000 := by
      calc δ ^ (ω / 20) ≤ D ^ (ω / 20) := Real.rpow_le_rpow hδ.le hδD (by positivity)
        _ = 1 / 19200000 := by
          dsimp [D]
          rw [← Real.rpow_mul (by norm_num)]
          rw [show 20 / ω * (ω / 20) = 1 by field_simp]
          simp
    have hpow : δ ^ (24 * ω / 25 - 2 * h) ≤ δ ^ (9 * ω / 10 + ω / 20) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hupper : 19200000 * δ ^ (24 * ω / 25 - 2 * h) ≤ δ ^ (9 * ω / 10) := by
      calc 19200000 * δ ^ (24 * ω / 25 - 2 * h)
          ≤ 19200000 * δ ^ (9 * ω / 10 + ω / 20) := by gcongr
        _ = δ ^ (9 * ω / 10) * (19200000 * δ ^ (ω / 20)) := by
          rw [Real.rpow_add hδ]
          ring
        _ ≤ δ ^ (9 * ω / 10) * 1 := by gcongr; linarith
        _ = _ := mul_one _
    have hsquare : (δ ^ (9 * ω / 20)) ^ 2 = δ ^ (9 * ω / 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      ring
    have hp : 0 < δ ^ (9 * ω / 20) := Real.rpow_pos_of_pos hδ _
    nlinarith
  · have hroot : 4 * δ ≤ δ ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ]
    have hpow : δ ^ (1 / 2 : ℝ) ≤ δ ^ (9 * ω / 20) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    exact (le_of_not_ge hc4).trans (hroot.trans hpow)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
