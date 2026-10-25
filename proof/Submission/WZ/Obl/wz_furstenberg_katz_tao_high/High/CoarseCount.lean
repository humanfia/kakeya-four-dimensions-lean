-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CoarseCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/CoarseCount.lean (c61cafd).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.SharedAssembly

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- The quadratic lower count inside each coarse tube gives a quadratic
upper count for the total coarse tubes, in terms of the tubes at one pin. -/
theorem coarse_count_arith {T K m C J R A : ℝ}
    (hT : 0 ≤ T) (hK : 0 < K) (hR : 0 ≤ R)
    (hcount : T * (m / K) ^ 2 ≤ C * J) (hbush : R ≤ A * (K * m)) :
    T * R ^ 2 ≤ K ^ 4 * C * J * A ^ 2 := by
  have hsquare := pow_le_pow_left₀ hR hbush 2
  calc
    _ ≤ T * (A * (K * m)) ^ 2 := mul_le_mul_of_nonneg_left hsquare hT
    _ = (K ^ 4 * A ^ 2) * (T * (m / K) ^ 2) := by field_simp
    _ ≤ (K ^ 4 * A ^ 2) * (C * J) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- The near-extremal fine line bound cancels the total fine bush size.
Consequently the number of coarse tubes is bounded by the square of the
number at one pin, with explicit losses. -/
theorem coarse_tube_count_le {r s ε₀ η η' c K : ℝ}
    {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hK : 0 < K)
    {cls tb : E2 × E2 → E2 × E2} {J₀ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hJcard : (J₀.card : ℝ) ≤ r ^ (-(2 * s) - ε₀))
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D)
    (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    (hbcls : Balanced S cls K) (hbpt : Balanced S (fun q => (q.1, tb (cls q))) K)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    {q : E2 × E2} (hq : q ∈ S) :
    ((S.image (fun a => tb (cls a))).card : ℝ) ≤
      K ^ 4 * tubeConst r s η c K * r ^ (-ε₀ - 2 * η') *
        ((pinTubes S cls tb q.1).card : ℝ) ^ 2 := by
  classical
  have hr := h.r_pos
  have hcount := shared_tubes_count h hs0 hs1 hc hK hclsJ hJ₀D hgeo hSD hbcls hbpt hfar hq
  have hpin := shared_tubes_pin hbpt hq
  have hsize := hS.D_card q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hh := coarse_count_arith (Nat.cast_nonneg _) hK
    (Real.rpow_nonneg hr.le _) hcount (hsize.trans hpin)
  have hC : 0 ≤ tubeConst r s η c K := tubeConst_nonneg hr hc hK.le
  have hJmul : K ^ 4 * tubeConst r s η c K * J₀.card * ((pinTubes S cls tb q.1).card : ℝ) ^ 2 ≤
      K ^ 4 * tubeConst r s η c K * r ^ (-(2 * s) - ε₀) *
        ((pinTubes S cls tb q.1).card : ℝ) ^ 2 := by
    gcongr
  have hpow : r ^ (-(2 * s) - ε₀) = r ^ (-ε₀ - 2 * η') * (r ^ (η' - s)) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  have htotal := hh.trans hJmul
  rw [hpow] at htotal
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (Real.rpow_pos_of_pos hr (η' - s)))).mp
  calc _ ≤ _ := htotal
    _ = _ := by ring

/-- Explicit power loss in the fine quadratic constant. -/
theorem tubeConst_le_power {r s η k ℓ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hη : 0 ≤ η) :
    tubeConst r s η (r ^ ℓ) (r ^ (-k)) ≤
      5200 * r ^ (-3 * η - 3 * k - ℓ * s) := by
  have hA : 1 ≤ r ^ (-η) := by
    calc 1 = r ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_nonpos.mpr hη)
  have hceil : ((⌈4 * r ^ (-η)⌉₊ : ℕ) : ℝ) ≤ 5 * r ^ (-η) := by
    have hh := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 * r ^ (-η))
    linarith
  have h52 : (52 : ℝ) ^ s ≤ 52 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 52) hs1
  unfold tubeConst
  calc
    _ ≤ 2 * (5 * r ^ (-η)) ^ 2 * (r ^ (-k)) ^ 3 *
        (2 * r ^ (-η) * (52 * (r ^ ℓ) ^ (-s))) := by gcongr
    _ = 5200 * r ^ (-3 * η - 3 * k - ℓ * s) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hr.le, ← Real.rpow_mul_natCast hr.le,
        ← Real.rpow_mul hr.le]
      ring_nf
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      ring

/-- The complete coefficient in the coarse tube count, as one power loss. -/
theorem coarse_count_coefficient_le {r s η η' ε₀ k ℓ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hη : 0 ≤ η) :
    (r ^ (-k)) ^ (4 : ℕ) * tubeConst r s η (r ^ ℓ) (r ^ (-k)) *
        r ^ (-ε₀ - 2 * η') ≤
      5200 * r ^ (-3 * η - 7 * k - ℓ * s - ε₀ - 2 * η') := by
  have hh := tubeConst_le_power (k := k) (ℓ := ℓ) hr hr1 hs1 hη
  calc
    _ ≤ (r ^ (-k)) ^ (4 : ℕ) * (5200 * r ^ (-3 * η - 3 * k - ℓ * s)) *
        r ^ (-ε₀ - 2 * η') := by gcongr
    _ = _ := by
      rw [← Real.rpow_mul_natCast hr.le]
      calc _ = 5200 * (r ^ ((-k) * (4 : ℕ)) * r ^ (-3 * η - 3 * k - ℓ * s) *
          r ^ (-ε₀ - 2 * η')) := by ring
        _ = _ := by
          rw [← Real.rpow_add hr, ← Real.rpow_add hr]
          congr 2
          ring

/-- The loss resulting from `regularize_two_ended` is linear in its small
parameters. In particular it tends to zero with them. -/
theorem regular_core_coefficient_le {r s η ε₀ ε ℓ : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hη : 0 ≤ η) :
    (r ^ (-2 * ε)) ^ (4 : ℕ) * tubeConst r s η (r ^ ℓ) (r ^ (-2 * ε)) *
        r ^ (-ε₀ - 2 * (9 * η + 8 * ε)) ≤
      5200 * r ^ (-(21 * η + 30 * ε + ε₀ + ℓ * s)) := by
  convert coarse_count_coefficient_le (ε₀ := ε₀) (η' := 9 * η + 8 * ε)
    (k := 2 * ε) (ℓ := ℓ) hr hr1 hs1 hη using 1 <;> congr 1 <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
