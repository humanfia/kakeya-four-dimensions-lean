-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.FarRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.FarTransversal

/-!
# Far rows of the energy

Two tubes form a *far* pair when their slab slopes differ by at least `b = 100 / c²`. For a
fixed tube, the far tubes whose height set `Z2` is nonempty and whose slope difference is at
most `2^k b` lie in a slab of width `O(c⁻² + 2^k b)`; with the refined transversality bound
`|Z2| ≤ 18 δ / |ΔslX|`, the dyadic sum of `|Z2|` over far tubes is `O((K+1) δ^-η n δ)`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN lineAt ctr slX Xc
  icX Zset CountF abs_lt_one_of_grainFib abs_sub_ctr_le_of_grainFib norm_lineAt_le coord_abs_le
  key_algebra tube_subset_slabW card_le_of_subset_slabW abs_slX_le)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (grainFib)

/-- Both fibres over `(u, z)` meet the tubes only for `z ∈ Z2`. -/
lemma pair_support_Z2 {δ : ℝ} {f : ℝ → ℝ} (hf : SlopeN f) {x v x' v' : Space}
    (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hT : tube δ x v ⊆ ball 0 1)
    (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|) {u z : ℝ}
    (hne : (grainFib f (tube δ x v) u z).Nonempty)
    (hne' : (grainFib f (tube δ x' v') u z).Nonempty) :
    z ∈ Z2 f δ x v x' v' ∧ |u - ctr f x v z| ≤ 3 * δ * (|f 0| + 3) := by
  have hz := abs_lt_one_of_grainFib hT hne
  have hM : |f z| ≤ |f 0| + 2 := by
    have hs := hf.sub_le hz.le
    have ha := abs_add_le (f z - f 0) (f 0)
    rw [sub_add_cancel] at ha
    linarith
  have h1 := abs_sub_ctr_le_of_grainFib hv hv2 hM hne
  have h2 := abs_sub_ctr_le_of_grainFib hv' hv2' hM hne'
  have hw : 3 * δ * (1 + (|f 0| + 2)) = 3 * δ * (|f 0| + 3) := by ring
  rw [hw] at h1 h2
  refine ⟨⟨abs_le.mp hz.le, ?_⟩, h1⟩
  calc |ctr f x v z - ctr f x' v' z| = |(u - ctr f x' v' z) - (u - ctr f x v z)| := by ring_nf
    _ ≤ |u - ctr f x' v' z| + |u - ctr f x v z| := abs_sub _ _
    _ ≤ 6 * δ * (|f 0| + 3) := by linarith

/-- `Z2` is contained in the coarse height set `Zset (27 r)` when `1 ≤ r c²`. -/
lemma Z2_subset_Zset {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hrc : 1 ≤ r * (f 0) ^ 2) {x v x' v' : Space}
    (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hT : tube δ x v ⊆ ball 0 1)
    (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|) (hT' : tube δ x' v' ⊆ ball 0 1) :
    Z2 f δ x v x' v' ⊆ Zset (f 0) (27 * r) x v x' v' := by
  intro z hz
  have hz1 : |z| ≤ 1 := abs_le.mpr hz.1
  refine ⟨hz.1, ?_⟩
  have hL := norm_lineAt_le hδ hv hv2 hT hz1
  have hL' := norm_lineAt_le hδ hv' hv2' hT' hz1
  have ha : |lineAt x v z 0 - lineAt x' v' z 0| ≤ 10 := by
    have h := coord_abs_le (lineAt x v z - lineAt x' v' z) 0
    rw [PiLp.sub_apply] at h
    exact h.trans ((norm_sub_le _ _).trans (by linarith))
  have hD : |(lineAt x v z 0 - lineAt x' v' z 0) +
      f z * (lineAt x v z 1 - lineAt x' v' z 1)| ≤ 6 * r * (|f 0| + 3) := by
    rw [← ctr_sub_eq]
    calc _ ≤ 6 * δ * (|f 0| + 3) := hz.2
      _ ≤ 6 * r * (|f 0| + 3) := by gcongr
  have hkey := key_algebra hc hrc (hδ.trans_le hδr) (hf.sub_le hz1) ha hD
  convert hkey using 1
  congr 1
  dsimp [Xc]
  ring

/-- Shell domination for far indices. -/
private lemma le_sum_shell_far {Zj Bj b κ : ℝ} {P : Prop} [Decidable P] (hb : 0 < b)
    (K : ℕ) (hZ0 : 0 ≤ Zj) (hBb : b ≤ |Bj|) (hZB : Zj * |Bj| ≤ 2 * κ)
    (hZP : ¬ P → Zj = 0) (hBK : |Bj| ≤ 2 ^ K * b) (hκ : 0 ≤ κ) :
    Zj ≤ ∑ k ∈ range (K + 1),
      (if P ∧ |Bj| ≤ 2 ^ k * b then 4 * κ / (2 ^ k * b) else 0) := by
  classical
  have hnonneg : ∀ k ∈ range (K + 1),
      0 ≤ (if P ∧ |Bj| ≤ 2 ^ k * b then 4 * κ / (2 ^ k * b) else (0 : ℝ)) := by
    intro k _
    split_ifs
    · positivity
    · exact le_rfl
  by_cases hP : P
  swap
  · rw [hZP hP]
    exact sum_nonneg hnonneg
  have hex : ∃ k, |Bj| ≤ 2 ^ k * b := ⟨K, hBK⟩
  set m := Nat.find hex with hm
  have hmspec : |Bj| ≤ 2 ^ m * b := Nat.find_spec hex
  have hmK : m ≤ K := Nat.find_min' hex hBK
  have hterm : (if P ∧ |Bj| ≤ 2 ^ m * b then 4 * κ / (2 ^ m * b) else (0 : ℝ)) =
      4 * κ / (2 ^ m * b) := by
    split_ifs with h
    · rfl
    · exact absurd ⟨hP, hmspec⟩ h
  have hB0 : 0 < |Bj| := hb.trans_le hBb
  have hZm : Zj ≤ 4 * κ / (2 ^ m * b) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, one_mul, le_div_iff₀ hb]
      have h2 : Zj * b ≤ Zj * |Bj| := mul_le_mul_of_nonneg_left hBb hZ0
      nlinarith
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hlt : ¬ |Bj| ≤ 2 ^ m' * b := Nat.find_min hex (by omega)
      push Not at hlt
      rw [hm', pow_succ, le_div_iff₀ (by positivity)]
      have h2 : Zj * (2 ^ m' * b) ≤ Zj * |Bj| := mul_le_mul_of_nonneg_left hlt.le hZ0
      nlinarith
  calc Zj ≤ 4 * κ / (2 ^ m * b) := hZm
    _ = (if P ∧ |Bj| ≤ 2 ^ m * b then 4 * κ / (2 ^ m * b) else (0 : ℝ)) := hterm.symm
    _ ≤ ∑ k ∈ range (K + 1),
          (if P ∧ |Bj| ≤ 2 ^ k * b then 4 * κ / (2 ^ k * b) else 0) :=
        single_le_sum hnonneg (mem_range.mpr (by omega))

/-- Dyadic summation over far indices. -/
lemma dyadic_far_sum {ι : Type*} (s : Finset ι) (Z B : ι → ℝ) (P : ι → Prop)
    [DecidablePred P] {b κ κ' D δ : ℝ} (hb : 0 < b) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (K : ℕ)
    (hZ0 : ∀ j ∈ s, 0 ≤ Z j) (hBb : ∀ j ∈ s, b ≤ |B j|)
    (hZB : ∀ j ∈ s, Z j * |B j| ≤ 2 * κ)
    (hZP : ∀ j ∈ s, ¬ P j → Z j = 0)
    (hBK : ∀ j ∈ s, |B j| ≤ 2 ^ K * b)
    (hcount : ∀ k : ℕ, ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * b)).card : ℝ) ≤
      D * (κ' + 2 * (2 ^ k * b) + 4 * δ)) :
    ∑ j ∈ s, Z j ≤ (K + 1) * (4 * κ * D * (κ' / b + 2 + 4 * δ / b)) := by
  classical
  calc ∑ j ∈ s, Z j
      ≤ ∑ j ∈ s, ∑ k ∈ range (K + 1),
          (if P j ∧ |B j| ≤ 2 ^ k * b then 4 * κ / (2 ^ k * b) else 0) := by
        refine sum_le_sum fun j hj => ?_
        exact le_sum_shell_far hb K (hZ0 j hj) (hBb j hj) (hZB j hj) (hZP j hj) (hBK j hj) hκ
    _ = ∑ k ∈ range (K + 1), ∑ j ∈ s,
          (if P j ∧ |B j| ≤ 2 ^ k * b then 4 * κ / (2 ^ k * b) else 0) := sum_comm
    _ = ∑ k ∈ range (K + 1),
          ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * b)).card : ℝ) * (4 * κ / (2 ^ k * b)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (K + 1), 4 * κ * D * (κ' / b + 2 + 4 * δ / b) := by
        refine sum_le_sum fun k _ => ?_
        have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have hpos : 0 < 2 ^ k * b := by positivity
        calc ((s.filter (fun j => P j ∧ |B j| ≤ 2 ^ k * b)).card : ℝ) * (4 * κ / (2 ^ k * b))
            ≤ D * (κ' + 2 * (2 ^ k * b) + 4 * δ) * (4 * κ / (2 ^ k * b)) :=
              mul_le_mul_of_nonneg_right (hcount k) (by positivity)
          _ = 4 * κ * D * ((κ' + 4 * δ) / (2 ^ k * b) + 2) := by
              field_simp
              ring
          _ ≤ 4 * κ * D * ((κ' + 4 * δ) / b + 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have : (κ' + 4 * δ) / (2 ^ k * b) ≤ (κ' + 4 * δ) / b :=
                div_le_div_of_nonneg_left (by positivity) hb (by nlinarith)
              linarith
          _ = 4 * κ * D * (κ' / b + 2 + 4 * δ / b) := by ring
    _ = (K + 1) * (4 * κ * D * (κ' / b + 2 + 4 * δ / b)) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Far rows.** For a fixed tube, the far tubes have total height-set length
`O((K+1) δ^-η n δ)`. -/
theorem far_row_bound {η δ : ℝ} (hδ : 0 < δ) {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1) (hF : CountF η δ n x v)
    {f : ℝ → ℝ} (hf : SlopeN f) (hc : 100 < |f 0|) (hδc : δ * (f 0) ^ 2 ≤ 1)
    (K : ℕ) (hK : 5 ≤ 2 ^ K * (100 / (f 0) ^ 2)) (i : Fin n) :
    ∑ j ∈ univ.filter (fun j => 100 / (f 0) ^ 2 ≤ |slX (f 0) (v i) - slX (f 0) (v j)|),
      (volume (Z2 f δ (x i) (v i) (x j) (v j))).toReal ≤
        (K + 1) * (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)) := by
  classical
  set c := f 0 with hcdef
  have hc0 : 0 < |c| := by linarith
  have hc2 : 0 < c ^ 2 := by
    have : c ≠ 0 := abs_pos.mp hc0
    positivity
  set b := 100 / c ^ 2 with hbdef
  set r := 1 / c ^ 2 with hrdef
  have hb : 0 < b := by positivity
  have hr : 0 < r := by positivity
  have hrc : 1 ≤ r * c ^ 2 := by rw [hrdef, div_mul_cancel₀ _ hc2.ne']
  have hδr : δ ≤ r := by rw [hrdef, le_div_iff₀ hc2]; linarith
  have hD : (0 : ℝ) ≤ 8 * δ ^ (-η) * n := by positivity
  have h := dyadic_far_sum
    (univ.filter (fun j => b ≤ |slX c (v i) - slX c (v j)|))
    (fun j => (volume (Z2 f δ (x i) (v i) (x j) (v j))).toReal)
    (fun j => slX c (v i) - slX c (v j))
    (fun j => (Zset c (27 * r) (x i) (v i) (x j) (v j)).Nonempty)
    (κ := 9 * δ) (κ' := 27 * r) (D := 8 * δ ^ (-η) * n) (δ := δ)
    hb (by positivity) (by positivity) hD hδ.le K ?_ ?_ ?_ ?_ ?_ ?_
  · calc _ ≤ (K + 1) * (4 * (9 * δ) * (8 * δ ^ (-η) * n) * (27 * r / b + 2 + 4 * δ / b)) := h
      _ ≤ (K + 1) * (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)) := by
        have hcne : c ^ 2 ≠ 0 := hc2.ne'
        have h1 : 27 * r / b = 27 / 100 := by
          rw [hrdef, hbdef, div_div_eq_mul_div, mul_one_div, div_mul_eq_mul_div,
            mul_div_assoc, div_self hcne, mul_one]
        have h2 : 4 * δ / b ≤ 4 / 100 := by
          rw [hbdef, div_div_eq_mul_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
          nlinarith
        have hK0 : (0 : ℝ) ≤ K + 1 := by positivity
        rw [h1]
        have : 4 * (9 * δ) * (8 * δ ^ (-η) * n) = 36 * δ * (8 * δ ^ (-η) * n) := by ring
        rw [this]
        gcongr
  · intro j _
    exact ENNReal.toReal_nonneg
  · intro j hj
    exact (mem_filter.mp hj).2
  · intro j hj
    have hB := (mem_filter.mp hj).2
    have hvol := volume_Z2_le_of_slope hδ hf hc hδc (hv i) (hv2 i) (hT i) (hv j) (hv2 j) (hT j) hB
    have hB0 : 0 < |slX c (v i) - slX c (v j)| := hb.trans_le hB
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
    rw [le_div_iff₀ hB0] at h1
    linarith
  · intro j _ hne
    have hsub := Z2_subset_Zset hδ hδr hf hc hrc (hv i) (hv2 i) (hT i) (hv j) (hv2 j) (hT j)
    have hempty : Z2 f δ (x i) (v i) (x j) (v j) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      exact subset_empty_iff.mp (hne ▸ hsub)
    simp [hempty]
  · intro j _
    have h1 := abs_slX_le hc (hv i) (hv2 i)
    have h2 := abs_slX_le hc (hv j) (hv2 j)
    calc |slX c (v i) - slX c (v j)| ≤ |slX c (v i)| + |slX c (v j)| := abs_sub _ _
      _ ≤ 5 := by linarith
      _ ≤ 2 ^ K * b := hK
  · intro k
    have hρ : 0 ≤ 27 * r + 2 * (2 ^ k * b) + 4 * δ := by positivity
    have hcard := card_le_of_subset_slabW hF hδ hρ
      ((univ.filter (fun j => b ≤ |slX c (v i) - slX c (v j)|)).filter
        (fun j => (Zset c (27 * r) (x i) (v i) (x j) (v j)).Nonempty ∧
          |slX c (v i) - slX c (v j)| ≤ 2 ^ k * b))
      (c := c) (α := icX c (x i) (v i)) (β := slX c (v i)) (by
        intro j hj
        rw [mem_filter] at hj
        exact tube_subset_slabW hδ hc (hv j) (hv2 j) (hT j) hj.2.1 hj.2.2)
    calc _ ≤ δ ^ (-η) * n * (8 * (27 * r + 2 * (2 ^ k * b) + 4 * δ)) := hcard
      _ = 8 * δ ^ (-η) * n * (27 * r + 2 * (2 ^ k * b) + 4 * δ) := by ring

end WangZahlLot.Obl.wz_intermediate_twist_normalization
