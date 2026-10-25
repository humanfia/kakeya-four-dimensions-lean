-- Adapted from: here:o004
import Mathlib

/-! Weighted cell energies and positive quadratic level decomposition. -/

namespace Submission.Lib.K4WeightedCellEnergy

open scoped BigOperators

/-- Two integer partitions into adjacent pairs capture every neighboring pair. -/
theorem neighboring_integer_grids {k l : ℤ} (hkl : k ≤ l + 1) (hlk : l ≤ k + 1) :
    k / 2 = l / 2 ∨ (k + 1) / 2 = (l + 1) / 2 := by
  omega

/-- The unit-cell indices of two points a distance at most one cell apart
differ by at most one. -/
theorem floor_neighbor_of_dist_le {r x y : ℝ} (hr : 0 < r) (hxy : |x - y| ≤ r) :
    ⌊x / r⌋ ≤ ⌊y / r⌋ + 1 ∧ ⌊y / r⌋ ≤ ⌊x / r⌋ + 1 := by
  have hab := abs_le.mp hxy
  have hxlo := Int.floor_le (x / r)
  have hxhi := Int.lt_floor_add_one (x / r)
  have hylo := Int.floor_le (y / r)
  have hyhi := Int.lt_floor_add_one (y / r)
  have hx : (⌊x / r⌋ : ℝ) * r ≤ x := (le_div_iff₀ hr).mp hxlo
  have hy : (⌊y / r⌋ : ℝ) * r ≤ y := (le_div_iff₀ hr).mp hylo
  have hx' : x < ((⌊x / r⌋ : ℝ) + 1) * r := (div_lt_iff₀ hr).mp hxhi
  have hy' : y < ((⌊y / r⌋ : ℝ) + 1) * r := (div_lt_iff₀ hr).mp hyhi
  constructor
  · have hh : (⌊x / r⌋ : ℝ) < (⌊y / r⌋ : ℝ) + 2 := by nlinarith
    have hh' : ⌊x / r⌋ < ⌊y / r⌋ + 2 := by exact_mod_cast hh
    omega
  · have hh : (⌊y / r⌋ : ℝ) < (⌊x / r⌋ : ℝ) + 2 := by nlinarith
    have hh' : ⌊y / r⌋ < ⌊x / r⌋ + 2 := by exact_mod_cast hh
    omega


/-- The two overlapping grids dominate the approximate collision kernel also
for arbitrary nonnegative weights. -/
theorem weighted_approximate_grid {I : Type*} [DecidableEq I]
    (S : Finset I) (F w : I → ℝ) {r : ℝ} (hr : 0 < r)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, ∑ j ∈ S, if |F i - F j| ≤ r then w i * w j else 0) ≤
      ∑ e : Fin 2, ∑ i ∈ S, ∑ j ∈ S,
        if (⌊F i / r⌋ + (e : ℕ)) / 2 = (⌊F j / r⌋ + (e : ℕ)) / 2
          then w i * w j else 0 := by
  have hterm (i : I) (hi : i ∈ S) (j : I) (hj : j ∈ S) :
      (if |F i - F j| ≤ r then w i * w j else 0) ≤
        (if ⌊F i / r⌋ / 2 = ⌊F j / r⌋ / 2 then w i * w j else 0) +
        (if (⌊F i / r⌋ + 1) / 2 = (⌊F j / r⌋ + 1) / 2 then w i * w j else 0) := by
    have hnon : 0 ≤ w i * w j := mul_nonneg (hw i hi) (hw j hj)
    by_cases hclose : |F i - F j| ≤ r
    · rw [if_pos hclose]
      obtain ⟨hk, hl⟩ := floor_neighbor_of_dist_le hr hclose
      rcases neighboring_integer_grids hk hl with h | h
      · rw [if_pos h]
        exact le_add_of_nonneg_right (by split_ifs <;> positivity)
      · rw [if_pos h]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
    · rw [if_neg hclose]
      exact add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity)
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((if ⌊F i / r⌋ / 2 = ⌊F j / r⌋ / 2 then w i * w j else 0) +
          (if (⌊F i / r⌋ + 1) / 2 = (⌊F j / r⌋ + 1) / 2 then w i * w j else 0)) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i hi j hj))
    _ = _ := by simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one, add_zero, Finset.sum_add_distrib]

/-- A same-cell quadratic energy is a sum of squares of the fiber masses. -/
theorem weighted_cell_energy_eq {I K : Type*} [DecidableEq I] [DecidableEq K]
    (S : Finset I) (f : I → K) (w : I → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, if f i = f j then w i * w j else 0) =
      ∑ k ∈ S.image f, (∑ i ∈ S with f i = k, w i) ^ 2 := by
  classical
  let mass : K → ℝ := fun k => ∑ i ∈ S with f i = k, w i
  have hrow (i : I) : (∑ j ∈ S, if f i = f j then w i * w j else 0) =
      w i * mass (f i) := by
    dsimp [mass]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : f i = f j <;> simp [hh, eq_comm]
  simp_rw [hrow]
  calc
    _ = ∑ k ∈ S.image f, ∑ i ∈ S with f i = k, w i * mass (f i) :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ = ∑ k ∈ S.image f, mass k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ∑ i ∈ S with f i = k, w i * mass k := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = mass k * mass k := (Finset.sum_mul _ _ _).symm
        _ = _ := (pow_two _).symm

/-- Decomposing a weight into finitely many levels costs only the number of
levels in a same-cell quadratic energy. No sign restriction is needed. -/
theorem weighted_cell_energy_levels {I K L : Type*}
    [DecidableEq I] [DecidableEq K] [Fintype L]
    (S : Finset I) (f : I → K) (w : I → ℝ) (v : L → I → ℝ)
    (hdecomp : ∀ i ∈ S, w i = ∑ l : L, v l i) :
    (∑ i ∈ S, ∑ j ∈ S, if f i = f j then w i * w j else 0) ≤
      (Fintype.card L : ℝ) *
        ∑ l : L, ∑ i ∈ S, ∑ j ∈ S, if f i = f j then v l i * v l j else 0 := by
  classical
  simp_rw [weighted_cell_energy_eq]
  have hmass (k : K) : (∑ i ∈ S with f i = k, w i) =
      ∑ l : L, ∑ i ∈ S with f i = k, v l i := by
    calc
      _ = ∑ i ∈ S with f i = k, ∑ l : L, v l i :=
        Finset.sum_congr rfl (fun i hi => hdecomp i (Finset.mem_filter.mp hi).1)
      _ = _ := Finset.sum_comm
  calc
    _ = ∑ k ∈ S.image f, (∑ l : L, ∑ i ∈ S with f i = k, v l i) ^ 2 := by
      simp_rw [hmass]
    _ ≤ ∑ k ∈ S.image f, (Fintype.card L : ℝ) *
        ∑ l : L, (∑ i ∈ S with f i = k, v l i) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset L))
          (f := fun l => ∑ i ∈ S with f i = k, v l i))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]



/-- A level pair that contributes substantially to a weighted mixed energy
has substantial mass, and its cardinality is comparable to the inverse square
energy. Applying the same statement with the levels interchanged controls both. -/
theorem large_pair_forces_mass_and_size {p q N M Z C L θ : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hN : 0 < N) (hM : 0 < M)
    (hZ : 0 < Z) (hL : 0 < L) (hθ : 0 < θ)
    (hpMass : p * N ≤ C) (hqMass : q * M ≤ C)
    (hpSq : p ^ 2 * N ≤ Z) (hqSq : q ^ 2 * M ≤ Z)
    (henergy : θ * Z ≤ L * (p ^ 2 * N) * (q ^ 2 * M) * min N M) :
    θ / L ≤ (p * N) ^ 2 ∧
      θ / (L * Z) ≤ N ∧ N ≤ L * C ^ 4 / (θ * Z) := by
  have hmass : θ ≤ L * (p * N) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hZ).mp
    calc
      θ * Z ≤ L * (p ^ 2 * N) * (q ^ 2 * M) * min N M := henergy
      _ ≤ L * (p ^ 2 * N) * Z * N := by
        gcongr
        exact min_le_left N M
      _ = (L * (p * N) ^ 2) * Z := by ring
  have hlow : θ ≤ (L * Z) * N := by
    apply (mul_le_mul_iff_left₀ hZ).mp
    calc
      θ * Z ≤ L * (p ^ 2 * N) * (q ^ 2 * M) * min N M := henergy
      _ ≤ L * Z * Z * N := by
        gcongr
        exact min_le_left N M
      _ = ((L * Z) * N) * Z := by ring
  have hp2 : (p * N) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) hpMass 2
  have hq2 : (q * M) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) hqMass 2
  have hupp : (θ * Z) * N ≤ L * C ^ 4 := by
    calc
      _ ≤ (L * (p ^ 2 * N) * (q ^ 2 * M) * min N M) * N :=
        mul_le_mul_of_nonneg_right henergy hN.le
      _ ≤ (L * (p ^ 2 * N) * (q ^ 2 * M) * M) * N := by
        gcongr
        exact min_le_right N M
      _ = L * (p * N) ^ 2 * (q * M) ^ 2 := by ring
      _ ≤ L * C ^ 2 * C ^ 2 := by gcongr
      _ = L * C ^ 4 := by ring
  refine ⟨(div_le_iff₀ hL).mpr (by nlinarith only [hmass]),
    (div_le_iff₀ (mul_pos hL hZ)).mpr (by nlinarith only [hlow]), ?_⟩
  apply (le_div_iff₀ (mul_pos hθ hZ)).mpr
  simpa only [mul_comm N (θ * Z)] using hupp

/-- A level whose weights are bounded below inherits a normalized counting
bound from the original weighted sum. -/
theorem heavy_subset_count_bound {I : Type*} [DecidableEq I]
    (S A : Finset I) (P : I → Prop) [DecidablePred P] (w : I → ℝ) {l m D : ℝ}
    (hAS : A ⊆ S) (hm : 0 < m)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hl : ∀ i ∈ A, l ≤ w i)
    (hmass : m ≤ l * (A.card : ℝ))
    (hcap : (∑ i ∈ S with P i, w i) ≤ D) :
    ((A.filter P).card : ℝ) ≤ (D / m) * (A.card : ℝ) := by
  classical
  have hfilter : A.filter P ⊆ S.filter P := by
    intro i hi
    obtain ⟨hiA, hiP⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hAS hiA, hiP⟩
  have hweight : l * ((A.filter P).card : ℝ) ≤ D := by
    calc
      _ = ∑ _i ∈ A.filter P, l := by simp [mul_comm]
      _ ≤ ∑ i ∈ A.filter P, w i :=
        Finset.sum_le_sum (fun i hi => hl i (Finset.mem_filter.mp hi).1)
      _ ≤ ∑ i ∈ S.filter P, w i :=
        Finset.sum_le_sum_of_subset_of_nonneg hfilter
          (fun i hi _ => hw i (Finset.mem_filter.mp hi).1)
      _ ≤ D := hcap
  have hfinal : ((A.filter P).card : ℝ) ≤ D * (A.card : ℝ) / m := by
    apply (le_div_iff₀ hm).mpr
    calc
      _ = m * ((A.filter P).card : ℝ) := mul_comm _ _
      _ ≤ (l * (A.card : ℝ)) * ((A.filter P).card : ℝ) :=
        mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg _)
      _ = (l * ((A.filter P).card : ℝ)) * (A.card : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hweight (Nat.cast_nonneg _)
  convert hfinal using 1
  ring


end Submission.Lib.K4WeightedCellEnergy
