-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/RatioLaw.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# The restricted ratio law and its interval bound

Paper Lemma 7.3 restricts the parameter law `ν` to a subpower fraction `I'` of its mass and passes
to the ratios `t = κ/κ₀`; Lemma 7.4 then needs the interval (Frostman) bound for `t/R` at all
scales `h ≤ u ≤ 1`. Restriction costs the factor `1/ν(I')`; the dilation by `κ₀ R` turns a window of
radius `u` into an interval of length `2|κ₀|R u`, which is bounded by covering it with unit
intervals or enlarging it to length `h`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

noncomputable section

variable {m : ℕ}

/-- The `ν`-mass of the parameters in a set. -/
def wmass (ν κ : Fin m → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] : ℝ :=
  ∑ i, if κ i ∈ S then ν i else 0

theorem wmass_mono {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) (κ : Fin m → ℝ) {S T : Set ℝ}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (hST : S ⊆ T) :
    wmass ν κ S ≤ wmass ν κ T := by
  unfold wmass
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hS : κ i ∈ S
  · rw [ite_eq_left hS, ite_eq_left (hST hS)]
  · rw [ite_eq_right hS]; split_ifs <;> simp [hν i]

theorem wmass_nonneg {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) (κ : Fin m → ℝ) (S : Set ℝ)
    [DecidablePred (· ∈ S)] : 0 ≤ wmass ν κ S :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hν i]

/-- An interval bound at scales `[h, 1]` controls every interval. -/
theorem wmass_Icc_le {ν κ : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) {h K s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 < s) (hK : 0 ≤ K)
    (hint : ∀ y ℓ : ℝ, h ≤ ℓ → ℓ ≤ 1 → wmass ν κ (Set.Icc y (y + ℓ)) ≤ K * ℓ ^ s)
    (y ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    wmass ν κ (Set.Icc y (y + ℓ)) ≤ K * (ℓ + h) ^ s * (ℓ + 2) := by
  classical
  have hpos : 0 ≤ K * (ℓ + h) ^ s := mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
  by_cases hsmall : ℓ + h ≤ 1
  · calc wmass ν κ (Set.Icc y (y + ℓ)) ≤ wmass ν κ (Set.Icc y (y + (ℓ + h))) :=
          wmass_mono hν κ (Set.Icc_subset_Icc le_rfl (by linarith))
      _ ≤ K * (ℓ + h) ^ s := hint y (ℓ + h) (by linarith) hsmall
      _ ≤ K * (ℓ + h) ^ s * (ℓ + 2) := le_mul_of_one_le_right hpos (by linarith)
  · push Not at hsmall
    set N := ⌈ℓ⌉₊ + 1 with hN
    have hcov : ∀ z ∈ Set.Icc y (y + ℓ), ∃ j ∈ Finset.range N, z ∈ Set.Icc (y + j) (y + j + 1) := by
      intro z hz
      have h0 : 0 ≤ z - y := by linarith [hz.1]
      refine ⟨⌊z - y⌋₊, ?_, ?_⟩
      · rw [Finset.mem_range, hN, Nat.lt_succ_iff]
        exact (Nat.floor_mono (by linarith [hz.2] : z - y ≤ ℓ)).trans (Nat.floor_le_ceil _)
      · have f1 := Nat.floor_le h0
        have f2 := Nat.lt_floor_add_one (z - y)
        constructor <;> linarith
    have hwin : ∀ j : ℕ, wmass ν κ (Set.Icc (y + j) (y + j + 1)) ≤ K := by
      intro j
      have := hint (y + j) 1 hh1 le_rfl
      rwa [Real.one_rpow, mul_one] at this
    calc wmass ν κ (Set.Icc y (y + ℓ))
        ≤ ∑ j ∈ Finset.range N, wmass ν κ (Set.Icc (y + j) (y + j + 1)) := by
          unfold wmass
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with hi
          · obtain ⟨j, hj, hj'⟩ := hcov _ hi
            calc ν i = if κ i ∈ Set.Icc (y + j) (y + j + 1) then ν i else 0 := by rw [ite_eq_left hj']
              _ ≤ ∑ j ∈ Finset.range N, if κ i ∈ Set.Icc (y + j) (y + j + 1) then ν i else 0 :=
                Finset.single_le_sum (f := fun j : ℕ => if κ i ∈ Set.Icc (y + j) (y + j + 1)
                  then ν i else 0) (fun j _ => by split_ifs <;> simp [hν i]) hj
          · exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hν i]
      _ ≤ ∑ _j ∈ Finset.range N, K := Finset.sum_le_sum fun j _ => hwin j
      _ = N * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (ℓ + 2) * K := by
          have hNle : (N : ℝ) ≤ ℓ + 2 := by
            rw [hN]; push_cast
            linarith [Nat.ceil_lt_add_one hℓ]
          exact mul_le_mul_of_nonneg_right hNle hK
      _ ≤ K * (ℓ + h) ^ s * (ℓ + 2) := by
          have h1 : 1 ≤ (ℓ + h) ^ s := Real.one_le_rpow hsmall.le hs.le
          nlinarith [mul_nonneg (mul_nonneg hK (by linarith : (0 : ℝ) ≤ ℓ + 2)) (sub_nonneg.mpr h1)]


/-- **The restricted ratio law** satisfies the interval bound needed by Lemma 7.4. -/
theorem restricted_ratio_frostman {ν κ : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) {h K s : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (hint : ∀ y ℓ : ℝ, h ≤ ℓ → ℓ ≤ 1 → wmass ν κ (Set.Icc y (y + ℓ)) ≤ K * ℓ ^ s)
    (I' : Finset (Fin m)) (hI' : 0 < ∑ i ∈ I', ν i) {κ₀ R : ℝ} (hκ₀ : κ₀ ≠ 0) (hR : 0 < R)
    (x u : ℝ) (hu : h ≤ u) (hu1 : u ≤ 1) :
    (∑ i, if κ i / κ₀ / R ∈ Set.Icc (x - u) (x + u) then
      (if i ∈ I' then ν i / ∑ j ∈ I', ν j else 0) else 0) ≤
      K / (∑ j ∈ I', ν j) * (2 * |κ₀| * R + 2) ^ 2 * u ^ s := by
  classical
  set νI := ∑ j ∈ I', ν j with hνI
  set y := κ₀ * R * x - |κ₀| * R * u
  set ℓ := 2 * |κ₀| * R * u
  have hu0 : 0 < u := lt_of_lt_of_le hh hu
  have hκR : 0 < |κ₀| * R := mul_pos (abs_pos.mpr hκ₀) hR
  have hmem : ∀ i, κ i / κ₀ / R ∈ Set.Icc (x - u) (x + u) → κ i ∈ Set.Icc y (y + ℓ) := by
    intro i hi
    have h1 : |κ i / κ₀ / R - x| ≤ u := by rw [abs_le]; constructor <;> linarith [hi.1, hi.2]
    have h2 : |κ i - κ₀ * R * x| ≤ |κ₀| * R * u := by
      have e : κ i - κ₀ * R * x = (κ₀ * R) * (κ i / κ₀ / R - x) := by field_simp
      rw [e, abs_mul, abs_mul, abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left h1 hκR.le
    rw [abs_le] at h2
    constructor <;> linarith [h2.1, h2.2]
  have hpt : ∀ i, (if κ i / κ₀ / R ∈ Set.Icc (x - u) (x + u) then
      (if i ∈ I' then ν i / νI else 0) else 0) ≤ (if κ i ∈ Set.Icc y (y + ℓ) then ν i else 0) / νI := by
    intro i
    by_cases h1 : κ i / κ₀ / R ∈ Set.Icc (x - u) (x + u)
    · rw [ite_eq_left h1, ite_eq_left (hmem i h1)]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hν i) hI'.le
    · rw [ite_eq_right h1]
      exact div_nonneg (by split_ifs <;> simp [hν i]) hI'.le
  have hw := wmass_Icc_le hν hh hh1 hs hK hint y ℓ (by positivity)
  have hb1 : (ℓ + h) ^ s ≤ u ^ s * (2 * |κ₀| * R + 1) := by
    have e1 : ℓ + h ≤ u * (2 * |κ₀| * R + 1) := by
      have : ℓ = u * (2 * |κ₀| * R) := by ring
      rw [this]; nlinarith
    calc (ℓ + h) ^ s ≤ (u * (2 * |κ₀| * R + 1)) ^ s :=
          Real.rpow_le_rpow (by positivity) e1 hs.le
      _ = u ^ s * (2 * |κ₀| * R + 1) ^ s := Real.mul_rpow hu0.le (by positivity)
      _ ≤ u ^ s * (2 * |κ₀| * R + 1) := by
          gcongr
          calc (2 * |κ₀| * R + 1) ^ s ≤ (2 * |κ₀| * R + 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [hκR]) hs1
            _ = 2 * |κ₀| * R + 1 := Real.rpow_one _
  have hb2 : ℓ + 2 ≤ 2 * |κ₀| * R + 2 := by
    have : ℓ ≤ 2 * |κ₀| * R := by
      calc ℓ = 2 * |κ₀| * R * u := rfl
        _ ≤ 2 * |κ₀| * R * 1 := by gcongr
        _ = 2 * |κ₀| * R := mul_one _
    linarith
  calc (∑ i, if κ i / κ₀ / R ∈ Set.Icc (x - u) (x + u) then
        (if i ∈ I' then ν i / νI else 0) else 0)
      ≤ ∑ i, (if κ i ∈ Set.Icc y (y + ℓ) then ν i else 0) / νI := Finset.sum_le_sum fun i _ => hpt i
    _ = wmass ν κ (Set.Icc y (y + ℓ)) / νI := by rw [wmass, Finset.sum_div]
    _ ≤ K * (ℓ + h) ^ s * (ℓ + 2) / νI := by gcongr
    _ ≤ K * (u ^ s * (2 * |κ₀| * R + 1)) * (2 * |κ₀| * R + 2) / νI := by
        gcongr
    _ ≤ K / νI * (2 * |κ₀| * R + 2) ^ 2 * u ^ s := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hI']
        have : 0 ≤ K * u ^ s := mul_nonneg hK (Real.rpow_nonneg hu0.le _)
        nlinarith [mul_nonneg this (by positivity : (0 : ℝ) ≤ 2 * |κ₀| * R + 2)]

end

end Submission.Obl.k4_retained_edge_planar_rigidity
