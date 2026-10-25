-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Basic, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Basic.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Basic.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Basic.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, o106/x0358, branch x0358 at 06d22f71.
The original adaptation and source credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

set_option autoImplicit false

/-!
# Elementary bounds for zoomed trajectories (version 2)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`, files
`Jets/Basic.lean` and `Jets/Coarsen.lean` (the floor-bin counting lemmas are copied unchanged;
the coordinate bounds are re-proved for `y ∈ ℝ²`).

Dot products on `Fin 2 → ℝ`, sup norms, bounds on `zx`, `zy`, `zv`, `zS` for bounded
coefficients at times in `[0,1]`, Lipschitz bounds in the coefficients, and counting lemmas for
the floor bins met by a union of closed balls or by an interval.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-! ### Vectors of `ℝ²` -/

theorem dot_two (a b : Fin 2 → ℝ) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 := by
  simp [dotProduct, Fin.sum_univ_two]

theorem abs_le_norm {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

theorem norm_le_of_abs_le {n : ℕ} {v : Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |v i| ≤ C) :
    ‖v‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).mpr fun i => by rw [Real.norm_eq_abs]; exact h i

theorem abs_dot_le (a b : Fin 2 → ℝ) : |a ⬝ᵥ b| ≤ 2 * ‖a‖ * ‖b‖ := by
  rw [dot_two]
  have h0 : |a 0 * b 0| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul (abs_le_norm a 0) (abs_le_norm b 0) (abs_nonneg _)
      (norm_nonneg _)
  have h1 : |a 1 * b 1| ≤ ‖a‖ * ‖b‖ := by
    rw [abs_mul]; exact mul_le_mul (abs_le_norm a 1) (abs_le_norm b 1) (abs_nonneg _)
      (norm_nonneg _)
  calc |a 0 * b 0 + a 1 * b 1| ≤ |a 0 * b 0| + |a 1 * b 1| := abs_add_le _ _
    _ ≤ 2 * ‖a‖ * ‖b‖ := by linarith

/-- The other index of `Fin 2`. -/
theorem fin_two_eq (k i : Fin 2) : i = k ∨ i = Fin.rev k := by
  fin_cases k <;> fin_cases i <;> simp [Fin.rev]

theorem rev_ne (k : Fin 2) : Fin.rev k ≠ k := by
  fin_cases k <;> decide

theorem dot_split (a b : Fin 2 → ℝ) (k : Fin 2) :
    a ⬝ᵥ b = a k * b k + a (Fin.rev k) * b (Fin.rev k) := by
  rw [dot_two]
  fin_cases k
  · simp [Fin.rev]
  · simp [Fin.rev]; ring

/-! ### Coordinates -/

@[scoped simp] theorem zy_zero (c : Fin 7 → ℝ) (t : ℝ) : zy c t 0 = c 3 + c 4 * t := by simp [zy]

@[scoped simp] theorem zy_one (c : Fin 7 → ℝ) (t : ℝ) : zy c t 1 = c 5 + c 6 * t := by simp [zy]

@[scoped simp] theorem zv_zero (c : Fin 7 → ℝ) : zv c 0 = c 4 := by simp [zv]

@[scoped simp] theorem zv_one (c : Fin 7 → ℝ) : zv c 1 = c 6 := by simp [zv]

theorem zy_add (c : Fin 7 → ℝ) (s t : ℝ) : zy c s = zy c t + (s - t) • zv c := by
  ext i
  fin_cases i <;> simp [zy, zv] <;> ring

theorem abs_zx_le {c : Fin 7 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zx c t| ≤ 3 * K := by
  unfold zx
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  have ht0 := ht.1; have ht1 := ht.2
  have e1 : |c 1 * t| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (c 1)]
  have e2 : |c 2 * t ^ 2| ≤ K := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
    have : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [abs_nonneg (c 2)]
  calc |c 0 + c 1 * t + c 2 * t ^ 2| ≤ |c 0| + |c 1 * t| + |c 2 * t ^ 2| := by
        have := abs_add_le (c 0 + c 1 * t) (c 2 * t ^ 2)
        have := abs_add_le (c 0) (c 1 * t)
        linarith
    _ ≤ 3 * K := by linarith

/-- An affine coordinate `c a + c b t` at a time in `[0,1]`. -/
theorem abs_affine_le {u v K t : ℝ} (hu : |u| ≤ K) (hv : |v| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |u + v * t| ≤ 2 * K := by
  have e1 : |v * t| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht.1]; nlinarith [abs_nonneg v, ht.2]
  calc |u + v * t| ≤ |u| + |v * t| := abs_add_le _ _
    _ ≤ 2 * K := by linarith

theorem abs_zy_le {c : Fin 7 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin 2) : |zy c t i| ≤ 2 * K := by
  fin_cases i
  · simpa using abs_affine_le (hc 3) (hc 4) ht
  · simpa using abs_affine_le (hc 5) (hc 6) ht

theorem norm_zy_le {c : Fin 7 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖zy c t‖ ≤ 2 * K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc 0)
  exact norm_le_of_abs_le (by positivity) (abs_zy_le hc ht)

theorem norm_zv_le {c : Fin 7 → ℝ} {K : ℝ} (hc : ∀ e, |c e| ≤ K) : ‖zv c‖ ≤ K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc 0)
  refine norm_le_of_abs_le hK fun i => ?_
  fin_cases i
  · simpa using hc 4
  · simpa using hc 6

theorem abs_zS_le {F : ℝ → Fin 2 → ℝ} {c : Fin 7 → ℝ} {K t : ℝ} (hc : ∀ e, |c e| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hF : ‖F t‖ ≤ K) : |zS F c t| ≤ 4 * K ^ 2 + 3 * K := by
  unfold zS
  have hx := abs_zx_le hc ht
  have hy := norm_zy_le hc ht
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hF
  have hd := abs_dot_le (F t) (zy c t)
  calc |zx c t - F t ⬝ᵥ zy c t| ≤ |zx c t| + |F t ⬝ᵥ zy c t| := abs_sub _ _
    _ ≤ 3 * K + 2 * K * (2 * K) := by
        have : 2 * ‖F t‖ * ‖zy c t‖ ≤ 2 * K * (2 * K) := by gcongr
        linarith
    _ = 4 * K ^ 2 + 3 * K := by ring

/-! ### Lipschitz bounds in the coefficients -/

theorem abs_coeff_sub_le {c c' : Fin 7 → ℝ} {r : ℝ} (h : ‖c - c'‖ ≤ r) (e : Fin 7) :
    |c e - c' e| ≤ r := by
  have := abs_le_norm (c - c') e
  simpa using this.trans h

theorem abs_zy_sub_le {c c' : Fin 7 → ℝ} {r t : ℝ} (h : ‖c - c'‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1)
    (i : Fin 2) : |zy c t i - zy c' t i| ≤ 2 * r := by
  have hc := abs_coeff_sub_le h
  fin_cases i
  · have := abs_affine_le (hc 3) (hc 4) ht
    simp only [zy_zero, Fin.zero_eta]
    convert this using 2; ring
  · have := abs_affine_le (hc 5) (hc 6) ht
    simp only [zy_one, Fin.mk_one]
    convert this using 2; ring

theorem norm_zy_sub_le {c c' : Fin 7 → ℝ} {r t : ℝ} (h : ‖c - c'‖ ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖zy c t - zy c' t‖ ≤ 2 * r := by
  have hr : 0 ≤ r := le_trans (norm_nonneg _) h
  refine norm_le_of_abs_le (by positivity) fun i => ?_
  simpa using abs_zy_sub_le h ht i

theorem abs_zx_sub_le {c c' : Fin 7 → ℝ} {r t : ℝ} (h : ‖c - c'‖ ≤ r) (ht : t ∈ Icc (0 : ℝ) 1) :
    |zx c t - zx c' t| ≤ 3 * r := by
  have hc : ∀ e, |(c - c') e| ≤ r := fun e => by simpa using abs_coeff_sub_le h e
  have := abs_zx_le (c := c - c') (K := r) hc ht
  have e : zx (c - c') t = zx c t - zx c' t := by simp only [zx, Pi.sub_apply]; ring
  rwa [e] at this

theorem abs_zS_sub_le {F : ℝ → Fin 2 → ℝ} {c c' : Fin 7 → ℝ} {r t K : ℝ} (h : ‖c - c'‖ ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hF : ‖F t‖ ≤ K) : |zS F c t - zS F c' t| ≤ (3 + 4 * K) * r := by
  have hx := abs_zx_sub_le h ht
  have hy := norm_zy_sub_le h ht
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hF
  have e : zS F c t - zS F c' t = (zx c t - zx c' t) - F t ⬝ᵥ (zy c t - zy c' t) := by
    simp only [zS, dotProduct_sub]; ring
  rw [e]
  have hd := abs_dot_le (F t) (zy c t - zy c' t)
  calc |(zx c t - zx c' t) - F t ⬝ᵥ (zy c t - zy c' t)|
      ≤ |zx c t - zx c' t| + |F t ⬝ᵥ (zy c t - zy c' t)| := abs_sub _ _
    _ ≤ 3 * r + 2 * K * (2 * r) := by
        have : 2 * ‖F t‖ * ‖zy c t - zy c' t‖ ≤ 2 * K * (2 * r) := by gcongr
        linarith
    _ = (3 + 4 * K) * r := by ring

/-! ### Floor bins (copied from x0801's `Jets/Basic.lean` and `Jets/Coarsen.lean`) -/

/-- The floor bins of side `q` met by a closed ball of radius `q`: at most three. -/
theorem floor_mem_of_mem_closedBall {q x z : ℝ} (hq : 0 < q) (hx : x ∈ Metric.closedBall z q) :
    ⌊x / q⌋ ∈ ({⌊z / q⌋ - 1, ⌊z / q⌋, ⌊z / q⌋ + 1} : Finset ℤ) := by
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have h1 : z / q - 1 ≤ x / q := by
    rw [div_sub_one hq.ne', div_le_div_iff_of_pos_right hq]; linarith
  have h2 : x / q ≤ z / q + 1 := by
    rw [div_add_one hq.ne', div_le_div_iff_of_pos_right hq]; linarith
  have a1 : ⌊z / q⌋ - 1 ≤ ⌊x / q⌋ := by
    have : ⌊z / q - 1⌋ ≤ ⌊x / q⌋ := Int.floor_mono h1
    rwa [Int.floor_sub_one] at this
  have a2 : ⌊x / q⌋ ≤ ⌊z / q⌋ + 1 := by
    have : ⌊x / q⌋ ≤ ⌊z / q + 1⌋ := Int.floor_mono h2
    rwa [Int.floor_add_one] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A set of reals covered by `m` closed balls of radius `q` meets at most `3 m` floor bins of
side `q`. -/
theorem card_floor_image_le {S : Set ℝ} {q : ℝ} (hq : 0 < q) {m : ℕ} {z : Fin m → ℝ}
    (hS : S ⊆ ⋃ j, Metric.closedBall (z j) q) :
    ∃ B : Finset ℤ, B.card ≤ 3 * m ∧ ∀ x ∈ S, ⌊x / q⌋ ∈ B := by
  classical
  refine ⟨Finset.univ.biUnion (fun j => ({⌊z j / q⌋ - 1, ⌊z j / q⌋, ⌊z j / q⌋ + 1} : Finset ℤ)),
    ?_, ?_⟩
  · calc _ ≤ ∑ j : Fin m, (({⌊z j / q⌋ - 1, ⌊z j / q⌋, ⌊z j / q⌋ + 1} : Finset ℤ)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin m, 3 := Finset.sum_le_sum fun j _ => Finset.card_le_three
      _ = 3 * m := by simp [mul_comm]
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hS hx)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, floor_mem_of_mem_closedBall hq hj⟩

/-- The occupied scalar bins at one time: labelled scalar values in `[-A, A]` meet at most
`3 K (2A / q)^d` floor bins of side `q`. -/
theorem occupied_bins_le {S : Set ℝ} {ζ d K q A : ℝ} (hAD : IntervalAD ζ d K S)
    (hζq : ζ ≤ q) (hq : 0 < q) (hqA : q ≤ 2 * A) (hS : S ⊆ Icc (-A) A) :
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ 3 * (K * (2 * A / q) ^ d) ∧ ∀ x ∈ S, ⌊x / q⌋ ∈ B := by
  obtain ⟨m, z, hcov, hm⟩ := hAD q (2 * A) (-A) hζq hqA
  have hS' : S ⊆ ⋃ j, Metric.closedBall (z j) q := by
    intro x hx
    apply hcov
    refine ⟨hx, ?_⟩
    have := hS hx
    constructor <;> linarith [this.1, this.2]
  obtain ⟨B, hB, hmem⟩ := card_floor_image_le hq hS'
  refine ⟨B, ?_, hmem⟩
  calc (B.card : ℝ) ≤ 3 * m := by exact_mod_cast hB
    _ ≤ 3 * (K * (2 * A / q) ^ d) := by linarith

/-- Values of `⌊y / w⌋` for `y` within `δ` of `y₀`. -/
theorem floor_mem_Icc_of_abs_le {y y₀ δ w : ℝ} (hw : 0 < w) (h : |y - y₀| ≤ δ) :
    ⌊y / w⌋ ∈ Finset.Icc ⌊(y₀ - δ) / w⌋ ⌊(y₀ + δ) / w⌋ := by
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)

theorem card_Icc_floor_le {y₀ δ w : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) :
    ((Finset.Icc ⌊(y₀ - δ) / w⌋ ⌊(y₀ + δ) / w⌋).card : ℝ) ≤ 2 * δ / w + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le ((y₀ + δ) / w)
  have h2 := Int.lt_floor_add_one ((y₀ - δ) / w)
  have h3 : (y₀ + δ) / w - (y₀ - δ) / w = 2 * δ / w := by field_simp; ring
  have hle : (0 : ℤ) ≤ ⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋ := by
    have : ⌊(y₀ - δ) / w⌋ ≤ ⌊(y₀ + δ) / w⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hw.le)
    omega
  have hcast : (((⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋).toNat : ℕ) : ℝ) =
      ((⌊(y₀ + δ) / w⌋ + 1 - ⌊(y₀ - δ) / w⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hle
  rw [hcast]
  push_cast
  linarith

/-- The bin index of a point of the closed interval of length `q B` starting at `a`. -/
theorem exists_bin {a x q B : ℝ} (hq : 0 < q) (h0 : a ≤ x) (h1 : x ≤ a + q * B) :
    ∃ i : ℕ, i < ⌊B⌋₊ + 1 ∧ x ∈ Ico (a + i * q) (a + i * q + q) := by
  have hxa : 0 ≤ (x - a) / q := div_nonneg (by linarith) hq.le
  have hB : (x - a) / q ≤ B := by rw [div_le_iff₀ hq]; linarith
  refine ⟨⌊(x - a) / q⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hB), ?_, ?_⟩
  · have := Nat.floor_le hxa
    have := (le_div_iff₀ hq).mp this
    linarith
  · have := Nat.lt_floor_add_one ((x - a) / q)
    have := (div_lt_iff₀ hq).mp this
    linarith

theorem floor_add_one_le {B : ℝ} (hB : 0 ≤ B) : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ B + 1 := by
  push_cast; linarith [Nat.floor_le hB]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
