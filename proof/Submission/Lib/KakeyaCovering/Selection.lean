import Submission.Lib.KakeyaCovering.Dyadic
import Submission.Lib.KakeyaCovering.Packing

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Lib.KakeyaCovering

open WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate (dyadic dyadic_pos dyadic_le_one)

/-- Two outer-measure pigeonholes extract a finite separated family at one common
scale from a countable cover. The trajectories and their witnesses need not be measurable. -/
theorem exists_productive_dyadic_family
    {X : Type*} [MetricSpace X]
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : Bornology.IsBounded A)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ → X)
    {a s : ℝ} (ha : 0 < a) (haA : ENNReal.ofReal a ≤ volume A) (hs : 0 < s)
    (c : ℕ → X) (ρ : ℕ → ℝ) (N : ℕ)
    (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ dyadic N)
    (hsum : ∑' i, ENNReal.ofReal (ρ i ^ s) ≤ 1)
    (hcover : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, f u t ∈ ⋃ i, ball (c i) (ρ i)) :
    ∃ k : ℕ, N ≤ k ∧
      ∃ F : Finset (EuclideanSpace ℝ (Fin 3)), ∃ B : Finset ℕ,
        (↑F : Set _) ⊆ A ∧
        (∀ u ∈ F, ∀ v ∈ F, u ≠ v → dyadic k < dist u v) ∧
        a ≤ 64 * (F.card : ℝ) * ((k : ℝ) + 1) ^ 2 * dyadic k ^ 3 ∧
        (B.card : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * s) ∧
        (∀ i ∈ B, dyadic (k + 1) < ρ i ∧ ρ i ≤ dyadic k) ∧
        (∀ u ∈ F, ENNReal.ofReal (1 / (4 * ((k : ℝ) + 1) ^ 2)) ≤
          volume {t : ℝ | t ∈ Icc 0 1 ∧ f u t ∈ ⋃ i ∈ B, ball (c i) (ρ i)}) := by
  classical
  let D : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun k =>
    {u | u ∈ A ∧ ENNReal.ofReal (1 / (4 * ((k : ℝ) + 1) ^ 2)) ≤
      volume {t : ℝ | t ∈ Icc 0 1 ∧ f u t ∈ dyadicCover c ρ k}}
  have hDA : A ⊆ ⋃ k, D k := by
    intro u hu
    obtain ⟨k, hk⟩ := exists_dyadic_time_mass c ρ
      (fun i => ⟨(hρ i).1, (hρ i).2.trans (dyadic_le_one N)⟩) (f u) (hcover u hu)
    exact mem_iUnion.mpr ⟨k, hu, hk⟩
  have hsumD : ENNReal.ofReal a ≤ ∑' k, volume (D k) :=
    haA.trans ((measure_mono hDA).trans (measure_iUnion_le D))
  obtain ⟨k, hk⟩ := WangZahlLot.Seed.Kakeya.exists_le_of_le_tsum
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top hsumD
  have hmass : ENNReal.ofReal (a / (4 * ((k : ℝ) + 1) ^ 2)) ≤ volume (D k) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    exact hk
  have hDnonzero : volume (D k) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hmass).ne'
  have hNk : N ≤ k := by
    obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hDnonzero
    by_contra! hkN
    have hempty := dyadicCover_eq_empty_of_lt (c := c) (fun i => (hρ i).2) hkN
    have hbad := hu.2
    have hT : {t : ℝ | t ∈ Icc 0 1 ∧ f u t ∈ dyadicCover c ρ k} = ∅ := by
      simp [hempty]
    rw [hT, measure_empty] at hbad
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) hbad
  obtain ⟨F, hFD, hsep, hcount⟩ := exists_many_separated_slopes
    (hA.subset (show D k ⊆ A from fun _ hu => hu.1)) (dyadic_pos k) hmass
  obtain ⟨B, hB, hBcard⟩ := dyadicClass_card_le hs hsum k
  have hBeq : dyadicCover c ρ k = ⋃ i ∈ B, ball (c i) (ρ i) := by
    simp only [dyadicCover, ← hB, Finset.mem_coe]
  refine ⟨k, hNk, F, B, fun u hu => (hFD hu).1, hsep, ?_, hBcard, ?_, ?_⟩
  · have h := (div_le_iff₀ (by positivity : 0 < 4 * ((k : ℝ) + 1) ^ 2)).mp hcount
    calc
      a ≤ ((F.card : ℝ) * 16 * dyadic k ^ 3) * (4 * ((k : ℝ) + 1) ^ 2) := h
      _ = 64 * (F.card : ℝ) * ((k : ℝ) + 1) ^ 2 * dyadic k ^ 3 := by ring
  · intro i hi
    have hi' : i ∈ dyadicClass ρ k := by simpa only [← hB, Finset.mem_coe] using hi
    exact hi'
  · intro u hu
    simpa only [hBeq] using (hFD hu).2

end Submission.Lib.KakeyaCovering
