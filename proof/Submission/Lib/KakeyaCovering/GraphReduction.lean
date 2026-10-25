import Submission.Lib.KakeyaCovering.BallCover
import Submission.Lib.KakeyaCovering.Selection

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Lib.KakeyaCovering

open WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate (dyadic dyadic_pos)

/-- The DK4 interface, exactly as in the supplied preset split. -/
def DiscreteKakeyaEstimate : Prop :=
    ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ c : ℝ, 0 < c → ∀ R : ℝ, 1 ≤ R →
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 4)),
        c * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2 ≤ (n : ℝ) →
        (∀ i : Fin n, x i 0 = 0 ∧ v i 0 = 1 ∧ ‖v i‖ ≤ 2) →
        (∀ i j : Fin n, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖) →
        (∀ i : Fin n, ‖x i‖ ≤ R) →
      ∀ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin 4)) (ρ : Fin m → ℝ),
        (m : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) →
        (∀ j : Fin m, (2 : ℝ) ^ (-((k : ℤ) + 1)) < ρ j ∧ ρ j ≤ (2 : ℝ) ^ (-(k : ℤ))) →
        ¬ (∀ i : Fin n, ENNReal.ofReal (c / ((k : ℝ) + 1) ^ 2) ≤
            MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
              x i + t • v i ∈ ⋃ j : Fin m, Metric.ball (z j) (ρ j)})

/-- The conversion between the dyadic radius and the integer-power notation in DK4. -/
theorem dyadic_eq_two_zpow (k : ℕ) : dyadic k = (2 : ℝ) ^ (-(k : ℤ)) := by
  simp [dyadic, zpow_neg, one_div]

/-- The reciprocal cubic slope volume equals the number of dyadic slope cells. -/
theorem two_pow_mul_dyadic_cube (k : ℕ) :
    (2 : ℝ) ^ (3 * k) * dyadic k ^ 3 = 1 := by
  simp only [dyadic, one_div, ← pow_mul, inv_pow]
  rw [Nat.mul_comm k 3, mul_inv_cancel₀ (by positivity)]

/-- DK4 gives the Hausdorff lower bound for a bounded graph family with a
positive-outer-volume set of slopes. -/
theorem four_le_dimH_of_bounded_graph_family
    (hDiscrete : DiscreteKakeyaEstimate)
    (K : Set (EuclideanSpace ℝ (Fin 4)))
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : Bornology.IsBounded A)
    (hA0 : volume A ≠ 0)
    (x v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (R : ℝ) (hR : 1 ≤ R)
    (hcoords : ∀ u ∈ A, x u 0 = 0 ∧ v u 0 = 1 ∧ ‖v u‖ ≤ 2)
    (hx : ∀ u ∈ A, ‖x u‖ ≤ R)
    (hsep : ∀ u ∈ A, ∀ w ∈ A, dist u w ≤ ‖v u - v w‖)
    (hseg : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, x u + t • v u ∈ K) :
    (4 : ENNReal) ≤ dimH K := by
  classical
  by_contra! hdim
  obtain ⟨d, hKd, hd4⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hdim
  let s : ℝ≥0 := max 3 d
  have hs3 : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (le_max_left (3 : ℝ≥0) d)
  have hs4 : (s : ℝ) < 4 := by
    exact_mod_cast (max_lt (by norm_num : (3 : ℝ≥0) < 4)
      (by exact_mod_cast hd4 : d < 4))
  have hs : 0 < (s : ℝ) := by linarith
  have hKs : dimH K < (s : ENNReal) := hKd.trans_le (by
    exact_mod_cast (le_max_right (3 : ℝ≥0) d))
  have hnull : μH[(s : ℝ)] K = 0 := hausdorffMeasure_of_dimH_lt hKs
  let σ : ℝ := 4 - s
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith
  have hsσ : (s : ℝ) = 4 - σ := by dsimp [σ]; ring
  let a : ℝ := (volume A).toReal
  have hAfinite : volume A ≠ ⊤ := hA.measure_lt_top.ne
  have ha : 0 < a := ENNReal.toReal_pos hA0 hAfinite
  have haA : ENNReal.ofReal a ≤ volume A := by
    exact (ENNReal.ofReal_toReal hAfinite).le
  let ε : ℝ := min (a / 64) (1 / 4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεa : 64 * ε ≤ a := by have := min_le_left (a / 64) (1 / 4 : ℝ); dsimp [ε]; linarith
  have hεtime : ε ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N, hN⟩ := hDiscrete σ hσ hσ1 ε hε R hR
  obtain ⟨c, ρ, hρ, hcover, hsum⟩ :=
    exists_countable_ball_cover_of_hausdorffMeasure_eq_zero hs hnull (dyadic_pos N) zero_lt_one
  obtain ⟨k, hNk, F, B, hFA, hFsep, hFcount, hBcount, hBrad, htime⟩ :=
    exists_productive_dyadic_family A hA (fun u t => x u + t • v u) ha haA hs c ρ N hρ
      (by simpa using hsum) (fun u hu t ht => hcover (hseg u hu t ht))
  let eF : Fin F.card ≃ ↥F := F.equivFin.symm
  let u : Fin F.card → EuclideanSpace ℝ (Fin 3) := fun i => (eF i).val
  have hu (i : Fin F.card) : u i ∈ F := (eF i).property
  have huA (i : Fin F.card) : u i ∈ A := hFA (hu i)
  let eB : Fin B.card ≃ ↥B := B.equivFin.symm
  let b : Fin B.card → ℕ := fun i => (eB i).val
  have hb (i : Fin B.card) : b i ∈ B := (eB i).property
  have hballunion : (⋃ j : Fin B.card, ball (c (b j)) (ρ (b j))) =
      ⋃ j ∈ B, ball (c j) (ρ j) := by
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨b j, hb j, hj⟩
    · rintro ⟨j, hjB, hz⟩
      obtain ⟨i, hi⟩ := eB.surjective ⟨j, hjB⟩
      refine ⟨i, ?_⟩
      simpa only [b, hi] using hz
  have hcard : ε * (2 : ℝ) ^ (3 * k) / ((k : ℝ) + 1) ^ 2 ≤ (F.card : ℝ) := by
    have hsmall : ε ≤ (F.card : ℝ) * ((k : ℝ) + 1) ^ 2 * dyadic k ^ 3 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ (2 : ℝ) ^ (3 * k))
    apply (div_le_iff₀ (by positivity : 0 < ((k : ℝ) + 1) ^ 2)).mpr
    calc
      ε * (2 : ℝ) ^ (3 * k) ≤
          ((F.card : ℝ) * ((k : ℝ) + 1) ^ 2 * dyadic k ^ 3) * (2 : ℝ) ^ (3 * k) := hmul
      _ = (F.card : ℝ) * ((k : ℝ) + 1) ^ 2 := by
        calc
          _ = (F.card : ℝ) * ((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (3 * k) * dyadic k ^ 3) := by ring
          _ = _ := by rw [two_pow_mul_dyadic_cube, mul_one]
  have hsep' : ∀ i j : Fin F.card, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤
      ‖v (u i) - v (u j)‖ := by
    intro i j hij
    have hne : u i ≠ u j := by
      intro heq
      exact hij (eF.injective (Subtype.ext heq))
    rw [← dyadic_eq_two_zpow]
    exact (hFsep (u i) (hu i) (u j) (hu j) hne).le.trans
      (hsep (u i) (huA i) (u j) (huA j))
  have hrad' : ∀ j : Fin B.card, (2 : ℝ) ^ (-((k : ℤ) + 1)) < ρ (b j) ∧
      ρ (b j) ≤ (2 : ℝ) ^ (-(k : ℤ)) := by
    intro j
    have h := hBrad (b j) (hb j)
    simpa only [dyadic_eq_two_zpow, Nat.cast_add, Nat.cast_one] using h
  have hBcount' : (B.card : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) := by
    simpa only [← hsσ] using hBcount
  apply hN k hNk F.card (fun i => x (u i)) (fun i => v (u i)) hcard
    (fun i => hcoords (u i) (huA i)) hsep' (fun i => hx (u i) (huA i))
    B.card (fun j => c (b j)) (fun j => ρ (b j)) hBcount' hrad'
  intro i
  rw [hballunion]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (htime (u i) (hu i))
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < ((k : ℝ) + 1) ^ 2)).mpr
    (by linarith : ε ≤ 1 / 4) |>.trans_eq (by field_simp)

end Submission.Lib.KakeyaCovering
