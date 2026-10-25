-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.CoarseEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Core

/-!
# Energy at a coarse scale

The planar pair estimate can be used at any radius `r ≥ δ` for which
`1 ≤ r * (f 0)^2`. The fibre widths remain at the original radius `δ`.
This retains the offset gain discarded by the small-twist estimate.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate
open WangZahlLot.Obl.wz_grains_nonsingular_slices (grainFib grainFib_mono)

lemma coarse_pair_support {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {f : ℝ → ℝ} (hf : SlopeN f) (hc : 100 < |f 0|) (hrc : 1 ≤ r * (f 0) ^ 2)
    {x v x' v' : Space} (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|)
    (hT : tube δ x v ⊆ ball 0 1) (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|)
    (hT' : tube δ x' v' ⊆ ball 0 1) {u z : ℝ}
    (hne : (grainFib f (tube δ x v) u z).Nonempty)
    (hne' : (grainFib f (tube δ x' v') u z).Nonempty) :
    z ∈ Zset (f 0) (27 * r) x v x' v' ∧
      |u - ctr f x v z| ≤ 3 * δ * (|f 0| + 3) := by
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
  have hL := norm_lineAt_le hδ hv hv2 hT hz.le
  have hL' := norm_lineAt_le hδ hv' hv2' hT' hz.le
  have ha : |lineAt x v z 0 - lineAt x' v' z 0| ≤ 10 := by
    have h := coord_abs_le (lineAt x v z - lineAt x' v' z) 0
    rw [PiLp.sub_apply] at h
    exact h.trans ((norm_sub_le _ _).trans (by linarith))
  have hD : |(lineAt x v z 0 - lineAt x' v' z 0) +
      f z * (lineAt x v z 1 - lineAt x' v' z 1)| ≤ 6 * r * (|f 0| + 3) := by
    have heq : (lineAt x v z 0 - lineAt x' v' z 0) +
        f z * (lineAt x v z 1 - lineAt x' v' z 1) =
        (u - ctr f x' v' z) - (u - ctr f x v z) := by
      simp only [ctr]
      ring
    rw [heq]
    calc _ ≤ |u - ctr f x' v' z| + |u - ctr f x v z| := abs_sub _ _
      _ ≤ 6 * δ * (|f 0| + 3) := by linarith
      _ ≤ 6 * r * (|f 0| + 3) := by gcongr
  have hkey := key_algebra hc hrc (hδ.trans_le hδr) (hf.sub_le hz.le) ha hD
  convert hkey using 1
  congr 1
  dsimp [Xc]
  ring

lemma coarse_row_bound {η δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1) (hF : CountF η δ n x v)
    {c : ℝ} (hc : 100 < |c|) (K : ℕ) (hK : 5 ≤ 2 ^ K * r) (i : Fin n) :
    ∑ j, (volume (Zset c (27 * r) (x i) (v i) (x j) (v j))).toReal ≤
      (K + 1) * (δ ^ (-η) * n * 8 * (4 * (27 * r) * (27 * r + 4 * r) / r +
        8 * (27 * r))) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  apply dyadic_sum_le Finset.univ
    (fun j => (volume (Zset c (27 * r) (x i) (v i) (x j) (v j))).toReal)
    (fun j => slX c (v i) - slX c (v j))
    (fun j => (Zset c (27 * r) (x i) (v i) (x j) (v j)).Nonempty)
    hr (by linarith) (by positivity) K
  · intro j _
    exact ENNReal.toReal_nonneg
  · intro j _
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (volume_Zset_le_two _ _ _ _ _ _)
  · intro j _ hB
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
      (volume_Zset_le_div (κ := 27 * r) (x := x i) (x' := x j) hB)
    rwa [le_div_iff₀ (abs_pos.mpr hB)] at h
  · intro j _ hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp only [hne, measure_empty, ENNReal.toReal_zero]
  · intro j _
    have h1 := abs_slX_le hc (hv i) (hv2 i)
    have h2 := abs_slX_le hc (hv j) (hv2 j)
    exact (abs_sub _ _).trans (by linarith)
  · intro k
    have hρ : 0 ≤ 27 * r + 2 * (2 ^ k * r) + 4 * δ := by positivity
    have h := card_le_of_subset_slabW hF hδ hρ
      (Finset.univ.filter (fun j => (Zset c (27 * r) (x i) (v i) (x j) (v j)).Nonempty ∧
        |slX c (v i) - slX c (v j)| ≤ 2 ^ k * r))
      (c := c) (α := icX c (x i) (v i)) (β := slX c (v i)) (by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact tube_subset_slabW hδ hc (hv j) (hv2 j) (hT j) hj.2.1 hj.2.2)
    calc _ ≤ δ ^ (-η) * n * (8 * (27 * r + 2 * (2 ^ k * r) + 4 * δ)) := h
      _ ≤ δ ^ (-η) * n * 8 * (27 * r + 2 * (2 ^ k * r) + 4 * r) := by
        rw [mul_assoc _ 8]
        gcongr

lemma offset_fibre_strip_const {δ C : ℝ} (hδ : 0 < δ) (hC : 100 < C) :
    (6 * δ / (C - 2)) ^ 2 * (2 * (3 * δ * (C + 3))) ≤ 300 * δ ^ 3 / C := by
  have hC0 : 0 < C := by linarith
  have hC2 : 0 < C - 2 := by linarith
  rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hC0]
  have h1 : 216 * C * (C + 3) ≤ 300 * (C - 2) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (pow_nonneg hδ.le 3)]


/-- The energy estimate with separate fine and coarse radii. -/
theorem coarse_energy {η δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hF : CountF η δ n x v) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hrc : 1 ≤ r * (f 0) ^ 2)
    (K : ℕ) (hK : 5 ≤ 2 ^ K * r) :
    (∑ i, volume (Y i)) ^ 2 ≤ volume (proj f (⋃ i, Y i)) *
      ENNReal.ofReal (9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η)) := by
  let ℓ := 6 * δ / (|f 0| - 2)
  let w := 3 * δ * (|f 0| + 3)
  let R := (K + 1) * δ ^ (-η) * n * (28512 * r)
  have hr : 0 < r := hδ.trans_le hδr
  have hℓ : 0 ≤ ℓ := div_nonneg (by positivity) (by linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfc : Continuous f := hf.continuous
  have hlength : ∀ i u z, volume (grainFib f (Y i) u z) ≤ ENNReal.ofReal ℓ := by
    intro i u z
    by_cases hne : (grainFib f (tube δ (x i) (v i)) u z).Nonempty
    · have hz := abs_lt_one_of_grainFib (hT i) hne
      have hm : |f 0| - 2 ≤ |f z| := by
        have hs := hf.sub_le hz.le
        have ha := abs_sub_abs_le_abs_sub (f 0) (f z)
        rw [abs_sub_comm] at ha
        linarith
      exact (measure_mono (grainFib_mono (hYT i) u z)).trans
        (volume_grainFib_tube_le (hv i) (hv2 i) (by linarith) hm)
    · have he : grainFib f (Y i) u z = ∅ :=
        subset_empty_iff.mp ((Set.not_nonempty_iff_eq_empty.mp hne) ▸
          grainFib_mono (hYT i) u z)
      simp only [he, measure_empty, zero_le]
  have hpairs : ∀ i j, ∫⁻ q, fib f (Y i) q * fib f (Y j) q ≤
      ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
        volume (Zset (f 0) (27 * r) (x i) (v i) (x j) (v j)) := by
    intro i j
    apply lintegral_fib_mul_le hfc (hYm i) (hYm j) hℓ (hlength i) (hlength j)
      (φ := ctr f (x i) (v i))
    intro u z hi hj
    exact coarse_pair_support hδ hδr hf hc hrc (hv i) (hv2 i) (hT i)
      (hv j) (hv2 j) (hT j) (hi.mono (grainFib_mono (hYT i) u z))
      (hj.mono (grainFib_mono (hYT j) u z))
  have hrows : ∀ i, ∑ j, volume (Zset (f 0) (27 * r) (x i) (v i) (x j) (v j)) ≤
      ENNReal.ofReal R := by
    intro i
    have hfinite : ∀ j ∈ Finset.univ,
        volume (Zset (f 0) (27 * r) (x i) (v i) (x j) (v j)) ≠ ⊤ :=
      fun j _ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_Zset_le_two _ _ _ _ _ _)
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.mpr hfinite) hR,
      ENNReal.toReal_sum hfinite]
    convert coarse_row_bound hδ hδr hv hv2 hT hF hc K hK i using 1 <;> dsimp [R]
    field_simp
    ring
  have henergy : ∫⁻ q, (∑ i, fib f (Y i) q) ^ 2 ≤
      ENNReal.ofReal (9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η)) := by
    rw [lintegral_sum_fib_sq hfc hYm]
    calc
      (∑ i, ∑ j, ∫⁻ q, fib f (Y i) q * fib f (Y j) q) ≤ ∑ i, ∑ j, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
          volume (Zset (f 0) (27 * r) (x i) (v i) (x j) (v j)) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpairs i j
      _ = ∑ i, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
          ∑ j, volume (Zset (f 0) (27 * r) (x i) (v i) (x j) (v j)) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * ENNReal.ofReal R := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_right (hrows i) _
      _ = ENNReal.ofReal (n * (ℓ ^ 2 * (2 * w) * R)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          (n : ℝ) * (ℓ ^ 2 * (2 * w) * R) ≤ n * ((300 * δ ^ 3 / |f 0|) * R) := by
            gcongr
            exact offset_fibre_strip_const hδ hc
          _ = 8553600 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η) := by
            dsimp [R]
            ring
          _ ≤ 9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η) := by
            gcongr
            norm_num
  let A := toMeasurable volume (proj f (⋃ i, Y i))
  have hsupp : ∀ q, q ∉ A → (∑ i, fib f (Y i) q) = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro i _
    apply fib_eq_zero_of_notMem
    intro hi
    exact hq (subset_toMeasurable _ _ (image_mono (subset_iUnion Y i) hi))
  have hCS := sq_lintegral_le_of_support volume (measurableSet_toMeasurable _ _)
    (Finset.measurable_sum _ (fun i _ => measurable_fib hfc (hYm i))) hsupp
  have hmass : ∑ i, volume (Y i) = ∫⁻ q, ∑ i, fib f (Y i) q := by
    rw [lintegral_finsetSum _ (fun i _ => measurable_fib hfc (hYm i))]
    exact Finset.sum_congr rfl fun i _ => volume_eq_lintegral_fib hfc (hYm i)
  rw [hmass]
  exact hCS.trans (by
    change volume (toMeasurable volume (proj f (⋃ i, Y i))) * _ ≤ _
    rw [measure_toMeasurable]
    exact mul_le_mul_right henergy _)

end WangZahlLot.Obl.wz_intermediate_twist_normalization
