-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.Rescaled.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.Grains

/-!
# Grains decomposition: general scale and inside a coarse tube

* `grains_partition_ball`: `grains_partition` for `E ⊆ ball 0 R` and segments of length `≤ Λ`,
  by scaling and cutting segments into unit pieces.
* `grains_partition_tube`: for `E` inside a `ρ`-tube and `δ`-tubes contained in that `ρ`-tube,
  anisotropic grains of size `≈ δ × ρ s × s`, obtained by applying `grains_partition_ball` after a
  rotation taking the axis to a coordinate axis and the transverse scaling by `1/ρ` (WZ Cor 7.17,
  before planarity).
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
namespace Grains

open MeasureTheory
open scoped Pointwise

namespace BallAux

/-- Dilating a set of `Space` by `r ≥ 0` multiplies its volume by `r ^ 3`. -/
lemma volume_smul {r : ℝ} (hr : 0 ≤ r) (A : Set Space) :
    volume (r • A) = ENNReal.ofReal (r ^ 3) * volume A := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume hr, finrank_euclideanSpace_fin]

/-- Dilations map segments into segments. -/
lemma smul_mem_segment (r : ℝ) {a b q : Space} (hq : q ∈ segment ℝ a b) :
    r • q ∈ segment ℝ (r • a) (r • b) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hq
  exact ⟨α, β, hα, hβ, hαβ, by rw [smul_add, smul_comm r α a, smul_comm r β b]⟩

/-- Dilating by `r⁻¹` maps the `δ`-neighbourhood of a segment into the `δ / r`-neighbourhood of
the dilated segment. -/
lemma mem_thickening_segment_smul {r δ : ℝ} (hr : 0 < r) {a u p : Space}
    (hp : p ∈ Metric.thickening δ (segment ℝ a (a + u))) :
    r⁻¹ • p ∈ Metric.thickening (δ / r) (segment ℝ (r⁻¹ • a) (r⁻¹ • a + r⁻¹ • u)) := by
  rw [← smul_add]
  rw [Metric.mem_thickening_iff] at hp ⊢
  obtain ⟨q, hq, hpq⟩ := hp
  refine ⟨r⁻¹ • q, smul_mem_segment r⁻¹ hq, ?_⟩
  rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_eq_inv_mul]
  exact mul_lt_mul_of_pos_left hpq (inv_pos.mpr hr)

/-- The segment from `x` to `x + v` is covered by the `n` segments from `x + (k / n) v` to
`x + (k / n) v + (1 / n) v`, `k < n`. -/
lemma exists_mem_segment_piece {n : ℕ} (hn : 0 < n) {x v q : Space}
    (hq : q ∈ segment ℝ x (x + v)) :
    ∃ k : Fin n, q ∈ segment ℝ (x + (((k : ℕ) : ℝ) / n) • v)
      (x + (((k : ℕ) : ℝ) / n) • v + (1 / (n : ℝ)) • v) := by
  rw [segment_eq_image'] at hq
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have htn : 0 ≤ t * n := by positivity
  set k : ℕ := min ⌊t * n⌋₊ (n - 1) with hk
  have hkn : k < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
  have hk1 : (k : ℝ) ≤ t * n := by
    have h1 : (k : ℝ) ≤ ⌊t * n⌋₊ := by exact_mod_cast min_le_left _ _
    exact h1.trans (Nat.floor_le htn)
  have hk2 : t * n - k ≤ 1 := by
    rcases le_total ⌊t * n⌋₊ (n - 1) with h | h
    · rw [hk, min_eq_left h]
      have := Nat.lt_floor_add_one (t * n)
      linarith
    · rw [hk, min_eq_right h, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one]
      have : t * n ≤ n := by nlinarith
      linarith
  refine ⟨⟨k, hkn⟩, ?_⟩
  rw [segment_eq_image']
  refine ⟨t * n - k, ⟨by linarith, hk2⟩, ?_⟩
  simp only [add_sub_cancel_left]
  rw [smul_smul, add_assoc, ← add_smul]
  congr 2
  field_simp
  ring

end BallAux

theorem grains_partition_ball (ε : ℝ) (hε : 0 < ε) (R Λ : ℝ) (hR : 1 ≤ R) (hΛ : 1 ≤ Λ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
    ∀ E : Set Space, MeasurableSet E → E ⊆ Metric.ball (0 : Space) R →
    ∃ (s m : ℝ) (G : ℕ) (P : Fin G → Set Space) (c : Fin G → Space),
      δ ≤ s ∧ s ≤ 2 * R ∧ 0 ≤ m ∧
      (ENNReal.ofReal δ ≤ ENNReal.ofReal (s / R ^ 3) * volume E ∨ s = 2 * R) ∧
      (∀ j, MeasurableSet (P j) ∧ P j ⊆ E ∧ P j ⊆ Metric.closedBall (c j) (2 * s)) ∧
      (Pairwise fun j k => Disjoint (P j) (P k)) ∧
      (∀ j, ENNReal.ofReal m ≤ volume (P j) ∧ volume (P j) ≤ ENNReal.ofReal (2 * m)) ∧
      (∀ j, volume (P j) ≤ ENNReal.ofReal (K * δ * s ^ 2)) ∧
      ENNReal.ofReal (δ ^ ε / K) * volume E ≤ ∑ j, volume (P j) ∧
      ENNReal.ofReal m ≤ ENNReal.ofReal (K * s ^ 3) * volume E ∧
      ∀ x v : Space, ‖v‖ ≤ Λ →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P j).Nonempty}.ncard : ℝ) ≤
          K * δ ^ (-ε) / s := by
  classical
  obtain ⟨K₀, hK₀, d₀, hd₀, H₀⟩ := grains_partition ε hε
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hRne : R ≠ 0 := hR0.ne'
  set n : ℕ := ⌈Λ⌉₊ with hn_def
  have hΛn : Λ ≤ n := Nat.le_ceil Λ
  have hn1 : (1 : ℝ) ≤ n := hΛ.trans hΛn
  have hn0 : 0 < n := by exact_mod_cast lt_of_lt_of_le one_pos hn1
  have hRε : 1 ≤ R ^ ε := Real.one_le_rpow hR hε.le
  have hK₀0 : 0 < K₀ := lt_of_lt_of_le one_pos hK₀
  set K : ℝ := n * K₀ * R * R ^ ε with hK_def
  have hK₀K : K₀ * R ^ ε ≤ K := by
    rw [hK_def]
    have h1 : 1 ≤ (n : ℝ) * R := one_le_mul_of_one_le_of_one_le hn1 hR
    calc K₀ * R ^ ε = 1 * (K₀ * R ^ ε) := (one_mul _).symm
      _ ≤ ((n : ℝ) * R) * (K₀ * R ^ ε) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = n * K₀ * R * R ^ ε := by ring
  have hK₀K' : K₀ ≤ K := by
    calc K₀ = K₀ * 1 := (mul_one _).symm
      _ ≤ K₀ * R ^ ε := mul_le_mul_of_nonneg_left hRε hK₀0.le
      _ ≤ K := hK₀K
  have hK0 : 0 < K := lt_of_lt_of_le hK₀0 hK₀K'
  refine ⟨K, hK₀.trans hK₀K', d₀, hd₀, ?_⟩
  intro δ hδ hδd E hE hER
  set δ' : ℝ := δ / R with hδ'_def
  have hδ' : 0 < δ' := div_pos hδ hR0
  have hδ'd : δ' ≤ d₀ := (div_le_self hδ.le hR).trans hδd
  have hE' : MeasurableSet (R⁻¹ • E) := hE.const_smul_of_ne_zero (inv_ne_zero hRne)
  have hE'ball : R⁻¹ • E ⊆ Metric.ball (0 : Space) 1 := by
    rintro p ⟨e, he, rfl⟩
    have he' := hER he
    rw [mem_ball_zero_iff] at he' ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0]
    calc R⁻¹ * ‖e‖ < R⁻¹ * R := mul_lt_mul_of_pos_left he' (inv_pos.mpr hR0)
      _ = 1 := inv_mul_cancel₀ hRne
  obtain ⟨s', m', G, P', c', hs'1, hs'2, hm', hguth', hP', hdisj, hmass, hthin, hsum, hmE,
    hcross⟩ := H₀ δ' hδ' hδ'd (R⁻¹ • E) hE' hE'ball
  have hs'0 : 0 < s' := lt_of_lt_of_le hδ' hs'1
  have hs'ne : s' ≠ 0 := hs'0.ne'
  have hvolE : volume E = ENNReal.ofReal (R ^ 3) * volume (R⁻¹ • E) := by
    rw [← BallAux.volume_smul hR0.le, smul_inv_smul₀ hRne]
  have hRs : ENNReal.ofReal (R * s' / R ^ 3) * ENNReal.ofReal (R ^ 3) =
      ENNReal.ofReal R * ENNReal.ofReal s' := by
    rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hR0.le hs'0.le) (by positivity)),
      ← ENNReal.ofReal_mul hR0.le]
    congr 1
    field_simp
  refine ⟨R * s', R ^ 3 * m', G, fun j => R • P' j, fun j => R • c' j, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- `δ ≤ s`
    have h := hs'1
    rw [hδ'_def, div_le_iff₀ hR0] at h
    linarith
  · -- `s ≤ 2 R`
    nlinarith
  · -- `0 ≤ m`
    positivity
  · -- the Guth lower bound
    rcases hguth' with h | h
    · left
      rw [hvolE, ← mul_assoc, hRs, mul_assoc]
      calc ENNReal.ofReal δ = ENNReal.ofReal R * ENNReal.ofReal δ' := by
            rw [← ENNReal.ofReal_mul hR0.le, hδ'_def]
            congr 1
            field_simp
        _ ≤ ENNReal.ofReal R * (ENNReal.ofReal s' * volume (R⁻¹ • E)) := by gcongr
    · right
      rw [h]
      ring
  · -- measurability, inclusion in `E`, inclusion in a ball
    intro j
    obtain ⟨hPm, hPE, hPc⟩ := hP' j
    refine ⟨hPm.const_smul_of_ne_zero hRne, ?_, ?_⟩
    · calc R • P' j ⊆ R • (R⁻¹ • E) := Set.smul_set_mono hPE
        _ = E := smul_inv_smul₀ hRne E
    · calc R • P' j ⊆ R • Metric.closedBall (c' j) (2 * s') := Set.smul_set_mono hPc
        _ = Metric.closedBall (R • c' j) (‖R‖ * (2 * s')) := smul_closedBall' hRne _ _
        _ = Metric.closedBall (R • c' j) (2 * (R * s')) := by
          rw [Real.norm_eq_abs, abs_of_pos hR0]; ring_nf
  · -- disjointness
    intro j k hjk
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.smul_set_inter₀ hRne,
      Set.disjoint_iff_inter_eq_empty.mp (hdisj hjk), Set.smul_set_empty]
  · -- comparable masses
    intro j
    obtain ⟨h1, h2⟩ := hmass j
    rw [BallAux.volume_smul hR0.le]
    constructor
    · rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
    · calc ENNReal.ofReal (R ^ 3) * volume (P' j)
          ≤ ENNReal.ofReal (R ^ 3) * ENNReal.ofReal (2 * m') := by gcongr
        _ = ENNReal.ofReal (2 * (R ^ 3 * m')) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  · -- thinness
    intro j
    rw [BallAux.volume_smul hR0.le]
    calc ENNReal.ofReal (R ^ 3) * volume (P' j)
        ≤ ENNReal.ofReal (R ^ 3) * ENNReal.ofReal (K₀ * δ' * s' ^ 2) := by gcongr; exact hthin j
      _ = ENNReal.ofReal (R ^ 3 * (K₀ * δ' * s' ^ 2)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K * δ * (R * s') ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have h : R ^ 3 * (K₀ * δ' * s' ^ 2) = K₀ * (δ * (R * s') ^ 2) := by
          rw [hδ'_def]; field_simp
        rw [h, mul_assoc K]
        exact mul_le_mul_of_nonneg_right hK₀K' (by positivity)
  · -- total mass
    simp only [BallAux.volume_smul hR0.le]
    rw [← Finset.mul_sum]
    have hreal : δ ^ ε / K ≤ δ' ^ ε / K₀ := by
      rw [hδ'_def, Real.div_rpow hδ.le hR0.le, div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [mul_comm]
      exact hK₀K
    calc ENNReal.ofReal (δ ^ ε / K) * volume E
        ≤ ENNReal.ofReal (δ' ^ ε / K₀) * volume E :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
      _ = ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal (δ' ^ ε / K₀) * volume (R⁻¹ • E)) := by
          rw [hvolE]; ring
      _ ≤ ENNReal.ofReal (R ^ 3) * ∑ j, volume (P' j) := mul_le_mul_right hsum _
  · -- mass bound
    calc ENNReal.ofReal (R ^ 3 * m') = ENNReal.ofReal (R ^ 3) * ENNReal.ofReal m' :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal (K₀ * s' ^ 3) * volume (R⁻¹ • E)) :=
          mul_le_mul_right hmE _
      _ = ENNReal.ofReal (K₀ * s' ^ 3) * volume E := by rw [hvolE]; ring
      _ ≤ ENNReal.ofReal (K * (R * s') ^ 3) * volume E := by
          apply mul_le_mul_left _ _
          apply ENNReal.ofReal_le_ofReal
          have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
          have hKR : K₀ ≤ K * R ^ 3 := by
            calc K₀ ≤ K := hK₀K'
              _ = K * 1 := (mul_one _).symm
              _ ≤ K * R ^ 3 := mul_le_mul_of_nonneg_left hR3 hK0.le
          calc K₀ * s' ^ 3 ≤ (K * R ^ 3) * s' ^ 3 :=
                mul_le_mul_of_nonneg_right hKR (by positivity)
            _ = K * (R * s') ^ 3 := by ring
  · -- crossing number
    intro x v hv
    set y : Fin n → Space := fun k => R⁻¹ • (x + (((k : ℕ) : ℝ) / n) • v) with hy
    set w : Space := R⁻¹ • ((1 / (n : ℝ)) • v) with hw
    have hwn : ‖w‖ ≤ 1 := by
      rw [hw, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hR0,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      calc R⁻¹ * (1 / n * ‖v‖) ≤ 1 * (1 / n * ‖v‖) := by
            apply mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hR) (by positivity)
        _ = ‖v‖ / n := by ring
        _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hsub : {j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ R • P' j).Nonempty} ⊆
        ⋃ k : Fin n, {j | (Metric.thickening δ' (segment ℝ (y k) (y k + w)) ∩ P' j).Nonempty} := by
      intro j hj
      obtain ⟨p, hp1, hp2⟩ := hj
      rw [Metric.mem_thickening_iff] at hp1
      obtain ⟨q, hq, hpq⟩ := hp1
      obtain ⟨k, hk⟩ := BallAux.exists_mem_segment_piece hn0 hq
      obtain ⟨b, hb, rfl⟩ := hp2
      refine Set.mem_iUnion.mpr ⟨k, b, ?_, hb⟩
      have h := BallAux.mem_thickening_segment_smul hR0
        (Metric.mem_thickening_iff.mpr ⟨q, hk, hpq⟩)
      rw [inv_smul_smul₀ hRne] at h
      exact h
    have hcard : ∀ k : Fin n,
        (({j | (Metric.thickening δ' (segment ℝ (y k) (y k + w)) ∩ P' j).Nonempty}.ncard : ℕ) :
          ℝ) ≤ K₀ * δ' ^ (-ε) / s' := fun k => hcross (y k) w hwn
    have hδε : δ' ^ (-ε) = δ ^ (-ε) * R ^ ε := by
      rw [hδ'_def, Real.div_rpow hδ.le hR0.le, Real.rpow_neg hR0.le, div_inv_eq_mul]
    calc _ ≤ ((⋃ k : Fin n,
            {j | (Metric.thickening δ' (segment ℝ (y k) (y k + w)) ∩ P' j).Nonempty}).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub
      _ ≤ ∑ k : Fin n,
            (({j | (Metric.thickening δ' (segment ℝ (y k) (y k + w)) ∩ P' j).Nonempty}.ncard : ℕ) :
              ℝ) := by
          exact_mod_cast Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _k : Fin n, K₀ * δ' ^ (-ε) / s' := Finset.sum_le_sum fun k _ => hcard k
      _ = n * (K₀ * δ' ^ (-ε) / s') := by simp
      _ = K * δ ^ (-ε) / (R * s') := by
          rw [hδε, hK_def]
          field_simp

namespace TubeAux

/-- The linear map scaling by `a` orthogonally to `w` and fixing the direction `w`. -/
noncomputable def T (w : Space) (a : ℝ) : Space →ₗ[ℝ] Space where
  toFun u := a • u + ((1 - a) * inner ℝ w u) • w
  map_add' u v := by
    simp only [inner_add_right, mul_add, add_smul, smul_add]
    abel
  map_smul' r u := by
    simp only [RingHom.id_apply, real_inner_smul_right, smul_add, smul_smul]
    congr 2 <;> ring

lemma T_apply (w : Space) (a : ℝ) (u : Space) :
    T w a u = a • u + ((1 - a) * inner ℝ w u) • w := rfl

lemma inner_self_w (w : Space) (hw : ‖w‖ = 1) : inner ℝ w w = (1 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, hw]; norm_num

lemma det_T (w : Space) (hw : ‖w‖ = 1) (a : ℝ) : LinearMap.det (T w a) = a ^ 2 := by
  have hw2 := EuclideanSpace.real_norm_sq_eq w
  rw [hw, Fin.sum_univ_three] at hw2
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, T_apply, EuclideanSpace.inner_single_right]
  linear_combination (a ^ 2 * (1 - a)) * hw2.symm

lemma inner_T (w : Space) (hw : ‖w‖ = 1) (a : ℝ) (u : Space) :
    inner ℝ w (T w a u) = inner ℝ w u := by
  rw [T_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_self_w w hw]
  ring

lemma proj_T (w : Space) (hw : ‖w‖ = 1) (a : ℝ) (u : Space) :
    T w a u - (inner ℝ w (T w a u)) • w = a • (u - (inner ℝ w u) • w) := by
  rw [inner_T w hw, T_apply]
  module

lemma T_T (w : Space) (hw : ‖w‖ = 1) (a b : ℝ) (u : Space) :
    T w a (T w b u) = T w (a * b) u := by
  rw [T_apply w a, inner_T w hw, T_apply, T_apply]
  module

lemma T_one (w : Space) (u : Space) : T w 1 u = u := by
  rw [T_apply]; simp

lemma norm_sq_proj (w : Space) (hw : ‖w‖ = 1) (u : Space) :
    ‖u - (inner ℝ w u) • w‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ w u) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_self_w w hw, real_inner_comm u w]
  ring

lemma norm_proj_le (w : Space) (hw : ‖w‖ = 1) (u : Space) :
    ‖u - (inner ℝ w u) • w‖ ≤ ‖u‖ := by
  have h := norm_sq_proj w hw u
  have h0 := norm_nonneg (u - (inner ℝ w u) • w)
  have h1 := norm_nonneg u
  nlinarith [sq_nonneg (inner ℝ w u)]

lemma abs_inner_le (w : Space) (hw : ‖w‖ = 1) (u : Space) : |inner ℝ w u| ≤ ‖u‖ := by
  have := abs_real_inner_le_norm w u
  rwa [hw, one_mul] at this

lemma norm_sq_T (w : Space) (hw : ‖w‖ = 1) (a : ℝ) (u : Space) :
    ‖T w a u‖ ^ 2 = a ^ 2 * ‖u - (inner ℝ w u) • w‖ ^ 2 + (inner ℝ w u) ^ 2 := by
  rw [norm_sq_proj w hw, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, T_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_self_w w hw, real_inner_comm u w]
  ring

lemma norm_T_le (w : Space) (hw : ‖w‖ = 1) {a : ℝ} (ha : 1 ≤ a) (u : Space) :
    ‖T w a u‖ ≤ a * ‖u‖ := by
  have h := norm_sq_T w hw a u
  rw [norm_sq_proj w hw] at h
  have h0 := norm_nonneg (T w a u)
  have h1 := norm_nonneg u
  have ha2 : (1 : ℝ) ≤ a ^ 2 := by nlinarith
  have h3 : ‖T w a u‖ ^ 2 ≤ (a * ‖u‖) ^ 2 := by
    rw [h, mul_pow]
    nlinarith [sq_nonneg (inner ℝ w u)]
  by_contra hcon
  have hlt : a * ‖u‖ < ‖T w a u‖ := not_le.1 hcon
  have : 0 ≤ a * ‖u‖ := mul_nonneg (by linarith) h1
  nlinarith

lemma volume_image_T (w : Space) (hw : ‖w‖ = 1) (a : ℝ) (A : Set Space) :
    volume (T w a '' A) = ENNReal.ofReal (a ^ 2) * volume A := by
  rw [Measure.addHaar_image_linearMap, det_T w hw, abs_of_nonneg (sq_nonneg a)]

lemma volume_image_add (o : Space) (B : Set Space) :
    volume ((fun q => o + q) '' B) = volume B := by
  rw [Set.image_add_left, measure_preimage_add]

/-- A point of the `ρ`-tube around `segment y (y + w)`, in coordinates centred at the midpoint
`o = y + (1/2) • w` of the axis: transverse part `< ρ`, axial part `< 1/2 + ρ`. -/
lemma tube_coords (w : Space) (hw : ‖w‖ = 1) {ρ : ℝ} {y o p : Space}
    (ho : o = y + (1 / 2 : ℝ) • w) (hp : p ∈ Metric.thickening ρ (segment ℝ y (y + w))) :
    ‖(p - o) - (inner ℝ w (p - o)) • w‖ < ρ ∧ |inner ℝ w (p - o)| < 1 / 2 + ρ := by
  obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  rw [dist_eq_norm] at hdist
  set u := p - (y + t • (y + w - y)) with hu
  have hpo : p - o = u + (t - 1 / 2) • w := by rw [hu, ho]; module
  have hin : inner ℝ w (p - o) = inner ℝ w u + (t - 1 / 2) := by
    rw [hpo, inner_add_right, real_inner_smul_right, inner_self_w w hw, mul_one]
  have hpr : (p - o) - (inner ℝ w (p - o)) • w = u - (inner ℝ w u) • w := by
    rw [hin, hpo]; module
  refine ⟨?_, ?_⟩
  · rw [hpr]; exact lt_of_le_of_lt (norm_proj_le w hw u) hdist
  · rw [hin]
    have h1 := abs_inner_le w hw u
    have h2 : |t - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |inner ℝ w u + (t - 1 / 2)| ≤ |inner ℝ w u| + |t - 1 / 2| := abs_add_le _ _
      _ < ρ + 1 / 2 := by linarith
      _ = 1 / 2 + ρ := by ring

end TubeAux

open TubeAux in
theorem grains_partition_tube (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ d * ρ → ρ ≤ 1 →
    ∀ (y w : Space), ‖w‖ = 1 → ∀ E : Set Space, MeasurableSet E →
      E ⊆ Metric.thickening ρ (segment ℝ y (y + w)) →
    ∃ (s m : ℝ) (G : ℕ) (P : Fin G → Set Space) (c : Fin G → Space),
      δ / ρ ≤ s ∧ s ≤ 4 ∧ 0 ≤ m ∧
      (ENNReal.ofReal (8 * δ * ρ) ≤ ENNReal.ofReal s * volume E ∨ s = 4) ∧
      (∀ j, MeasurableSet (P j) ∧ P j ⊆ E ∧ ∀ p ∈ P j,
        ‖(p - c j) - (inner ℝ w (p - c j)) • w‖ ≤ 4 * ρ * s ∧ |inner ℝ w (p - c j)| ≤ 4 * s) ∧
      (Pairwise fun j k => Disjoint (P j) (P k)) ∧
      (∀ j, ENNReal.ofReal m ≤ volume (P j) ∧ volume (P j) ≤ ENNReal.ofReal (2 * m)) ∧
      (∀ j, volume (P j) ≤ ENNReal.ofReal (K * δ * ρ * s ^ 2)) ∧
      ENNReal.ofReal ((δ / ρ) ^ ε / K) * volume E ≤ ∑ j, volume (P j) ∧
      ENNReal.ofReal m ≤ ENNReal.ofReal (K * s ^ 3) * volume E ∧
      ∀ x v : Space, ‖v‖ = 1 →
        Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.thickening ρ (segment ℝ y (y + w)) →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P j).Nonempty}.ncard : ℝ) ≤
          K * (δ / ρ) ^ (-ε) / s := by
  obtain ⟨K₁, hK₁, d₁, hd₁, H⟩ := grains_partition_ball ε hε 2 3 (by norm_num) (by norm_num)
  refine ⟨K₁, hK₁, d₁, hd₁, ?_⟩
  intro δ ρ hδ hδρ hρ1 y w hw E hE hEsub
  have hρ : 0 < ρ := by
    by_contra h
    have h' : ρ ≤ 0 := not_lt.1 h
    nlinarith
  have hδ' : 0 < δ / ρ := div_pos hδ hρ
  have hδ'd : δ / ρ ≤ d₁ := (div_le_iff₀ hρ).2 hδρ
  have hρinv : 1 ≤ ρ⁻¹ := one_le_inv_iff₀.2 ⟨hρ, hρ1⟩
  -- the centre of the coarse tube and the rescaling maps
  obtain ⟨o, ho⟩ : ∃ o : Space, o = y + (1 / 2 : ℝ) • w := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Space → Space, ∀ p, Φ p = T w ρ⁻¹ (p - o) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Space → Space, ∀ q, Ψ q = o + T w ρ q := ⟨_, fun _ => rfl⟩
  have hΨΦ : ∀ p, Ψ (Φ p) = p := by
    intro p
    rw [hΨ, hΦ, T_T w hw, mul_inv_cancel₀ hρ.ne', T_one]
    abel
  have hΦΨ : ∀ q, Φ (Ψ q) = q := by
    intro q
    rw [hΦ, hΨ, add_sub_cancel_left, T_T w hw, inv_mul_cancel₀ hρ.ne', T_one]
  have hΦc : Continuous Φ := by
    have : Φ = fun p => T w ρ⁻¹ (p - o) := funext hΦ
    rw [this]
    exact (LinearMap.continuous_of_finiteDimensional _).comp (continuous_id.sub continuous_const)
  have hΨc : Continuous Ψ := by
    have : Ψ = fun q => o + T w ρ q := funext hΨ
    rw [this]
    exact continuous_const.add (LinearMap.continuous_of_finiteDimensional _)
  have hΨimg : ∀ A : Set Space, Ψ '' A = Φ ⁻¹' A := fun A =>
    congrFun (Set.image_eq_preimage_of_inverse hΦΨ hΨΦ) A
  have hΦimg : ∀ A : Set Space, Φ '' A = Ψ ⁻¹' A := fun A =>
    congrFun (Set.image_eq_preimage_of_inverse hΨΦ hΦΨ) A
  have hΨinj : Function.Injective Ψ := Function.LeftInverse.injective hΦΨ
  have hvol : ∀ A : Set Space, volume (Ψ '' A) = ENNReal.ofReal (ρ ^ 2) * volume A := by
    intro A
    have : Ψ '' A = (fun q => o + q) '' (T w ρ '' A) := by
      rw [Set.image_image]
      exact Set.image_congr fun q _ => hΨ q
    rw [this, volume_image_add, volume_image_T w hw]
  -- the rescaled set
  obtain ⟨E', hE'def⟩ : ∃ E' : Set Space, E' = Φ '' E := ⟨_, rfl⟩
  have hEE' : E = Ψ '' E' := by
    rw [hE'def, Set.image_image]
    simp only [hΨΦ, Set.image_id']
  have hvolE : volume E = ENNReal.ofReal (ρ ^ 2) * volume E' := by
    rw [← hvol E', ← hEE']
  have hE' : MeasurableSet E' := by
    rw [hE'def, hΦimg]
    exact hΨc.measurable hE
  have hE'sub : E' ⊆ Metric.ball 0 2 := by
    rw [hE'def]
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h1, h2⟩ := tube_coords w hw ho (hEsub hp)
    rw [mem_ball_zero_iff, hΦ]
    have hsq := norm_sq_T w hw ρ⁻¹ (p - o)
    have hX : ρ⁻¹ * ‖(p - o) - (inner ℝ w (p - o)) • w‖ < 1 := by
      rw [inv_mul_lt_iff₀ hρ, mul_one]; exact h1
    have hX0 : 0 ≤ ρ⁻¹ * ‖(p - o) - (inner ℝ w (p - o)) • w‖ := by positivity
    have hc := abs_lt.1 h2
    have hsq' : ‖T w ρ⁻¹ (p - o)‖ ^ 2 =
        (ρ⁻¹ * ‖(p - o) - (inner ℝ w (p - o)) • w‖) ^ 2 + (inner ℝ w (p - o)) ^ 2 := by
      rw [hsq, mul_pow]
    have hn := norm_nonneg (T w ρ⁻¹ (p - o))
    nlinarith
  obtain ⟨s, m', G, P', c', hs1, hs2, hm', hguth', hP', hdisj, hmass, hthin, htot, hmE, hcross⟩ :=
    H (δ / ρ) hδ' hδ'd E' hE' hE'sub
  have hs : 0 < s := lt_of_lt_of_le hδ' hs1
  refine ⟨s, ρ ^ 2 * m', G, fun j => Ψ '' P' j, fun j => Ψ (c' j), hs1, by linarith,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hguth' with h | h
    · left
      rw [hvolE, ← mul_assoc, ← ENNReal.ofReal_mul hs.le]
      calc ENNReal.ofReal (8 * δ * ρ) = ENNReal.ofReal (8 * ρ ^ 2) * ENNReal.ofReal (δ / ρ) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_div_assoc', eq_div_iff hρ.ne']
            ring
        _ ≤ ENNReal.ofReal (8 * ρ ^ 2) * (ENNReal.ofReal (s / 2 ^ 3) * volume E') := by gcongr
        _ = ENNReal.ofReal (s * ρ ^ 2) * volume E' := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring
    · right
      rw [h]
      norm_num
  · intro j
    obtain ⟨hPm, hPE, hPc⟩ := hP' j
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [hΨimg]; exact hΦc.measurable hPm
    · rw [hEE']; exact Set.image_mono hPE
    · rintro _ ⟨q, hq, rfl⟩
      have hq' := hPc hq
      rw [Metric.mem_closedBall, dist_eq_norm] at hq'
      have hdiff : Ψ q - Ψ (c' j) = T w ρ (q - c' j) := by
        rw [hΨ, hΨ, add_sub_add_left_eq_sub, map_sub]
      rw [hdiff, proj_T w hw, inner_T w hw, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      constructor
      · calc ρ * ‖(q - c' j) - inner ℝ w (q - c' j) • w‖ ≤ ρ * ‖q - c' j‖ :=
              mul_le_mul_of_nonneg_left (norm_proj_le w hw _) hρ.le
          _ ≤ ρ * (2 * s) := mul_le_mul_of_nonneg_left hq' hρ.le
          _ ≤ 4 * ρ * s := by nlinarith
      · calc |inner ℝ w (q - c' j)| ≤ ‖q - c' j‖ := abs_inner_le w hw _
          _ ≤ 2 * s := hq'
          _ ≤ 4 * s := by linarith
  · intro j k hjk
    exact (Set.disjoint_image_iff hΨinj).2 (hdisj hjk)
  · intro j
    obtain ⟨h1, h2⟩ := hmass j
    dsimp only
    rw [hvol]
    constructor
    · rw [ENNReal.ofReal_mul (sq_nonneg ρ)]
      gcongr
    · calc ENNReal.ofReal (ρ ^ 2) * volume (P' j)
          ≤ ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (2 * m') := by gcongr
        _ = ENNReal.ofReal (2 * (ρ ^ 2 * m')) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg ρ)]; ring_nf
  · intro j
    dsimp only
    rw [hvol]
    calc ENNReal.ofReal (ρ ^ 2) * volume (P' j)
        ≤ ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (K₁ * (δ / ρ) * s ^ 2) := by gcongr; exact hthin j
      _ = ENNReal.ofReal (K₁ * δ * ρ * s ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg ρ)]
        congr 1
        field_simp
  · simp only [hvol]
    rw [← Finset.mul_sum, hvolE, mul_left_comm]
    gcongr
  · rw [hvolE, ENNReal.ofReal_mul (sq_nonneg ρ), mul_left_comm]
    gcongr
  · intro x v hv hsub
    dsimp only
    -- the image of the `δ`-tube lies in a `δ / ρ`-tube of the rescaled picture
    have hxv : ∀ p ∈ Metric.thickening δ (segment ℝ x (x + v)),
        Φ p ∈ Metric.thickening (δ / ρ) (segment ℝ (Φ x) (Φ x + T w ρ⁻¹ v)) := by
      intro p hp
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hp
      rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      refine Metric.mem_thickening_iff.2 ⟨Φ (x + t • (x + v - x)), ?_, ?_⟩
      · rw [segment_eq_image']
        refine ⟨t, ht, ?_⟩
        simp only [hΦ, add_sub_cancel_left, map_sub, map_add, map_smul]
        abel
      · rw [dist_eq_norm] at hdist ⊢
        have : Φ p - Φ (x + t • (x + v - x)) = T w ρ⁻¹ (p - (x + t • (x + v - x))) := by
          rw [hΦ, hΦ, ← map_sub]
          congr 1
          abel
        rw [this]
        calc ‖T w ρ⁻¹ (p - (x + t • (x + v - x)))‖
            ≤ ρ⁻¹ * ‖p - (x + t • (x + v - x))‖ := norm_T_le w hw hρinv _
          _ < ρ⁻¹ * δ := mul_lt_mul_of_pos_left hdist (inv_pos.2 hρ)
          _ = δ / ρ := by rw [inv_mul_eq_div]
    -- the rescaled direction has length `≤ 3`
    have hLv : ‖T w ρ⁻¹ v‖ ≤ 3 := by
      have hx := tube_coords w hw ho
        (hsub (Metric.self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))))
      have hx' := tube_coords w hw ho
        (hsub (Metric.self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))))
      have hpv : v - inner ℝ w v • w = ((x + v - o) - inner ℝ w (x + v - o) • w) -
          ((x - o) - inner ℝ w (x - o) • w) := by
        simp only [inner_sub_right, inner_add_right]
        module
      have hprv : ‖v - inner ℝ w v • w‖ < 2 * ρ := by
        rw [hpv]
        calc _ ≤ _ := norm_sub_le _ _
          _ < ρ + ρ := add_lt_add hx'.1 hx.1
          _ = 2 * ρ := by ring
      have hsq := norm_sq_T w hw ρ⁻¹ v
      have hcv : |inner ℝ w v| ≤ 1 := (abs_inner_le w hw v).trans hv.le
      have hX : ρ⁻¹ * ‖v - inner ℝ w v • w‖ < 2 := by
        rw [inv_mul_lt_iff₀ hρ]; linarith
      have hX0 : 0 ≤ ρ⁻¹ * ‖v - inner ℝ w v • w‖ := by positivity
      have hsq' : ‖T w ρ⁻¹ v‖ ^ 2 =
          (ρ⁻¹ * ‖v - inner ℝ w v • w‖) ^ 2 + (inner ℝ w v) ^ 2 := by
        rw [hsq, mul_pow]
      have hc := abs_le.1 hcv
      have hn := norm_nonneg (T w ρ⁻¹ v)
      nlinarith
    have hsubset : {j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ Ψ '' P' j).Nonempty} ⊆
        {j | (Metric.thickening (δ / ρ) (segment ℝ (Φ x) (Φ x + T w ρ⁻¹ v)) ∩ P' j).Nonempty} := by
      rintro j ⟨_, hp1, ⟨q, hq, rfl⟩⟩
      exact ⟨q, by rw [← hΦΨ q]; exact hxv _ hp1, hq⟩
    calc ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ Ψ '' P' j).Nonempty}.ncard : ℝ)
        ≤ ({j | (Metric.thickening (δ / ρ) (segment ℝ (Φ x) (Φ x + T w ρ⁻¹ v)) ∩
            P' j).Nonempty}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsubset
      _ ≤ K₁ * (δ / ρ) ^ (-ε) / s := hcross _ _ hLv

end Grains
end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
