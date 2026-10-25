-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Pairs
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Dyadic

/-!
# The core energy estimate

For a transverse family satisfying the convex count, and a slope function with
`100 < |f 0|` and `1 ≤ δ (f 0)²`, the square of the shading mass is at most the projected
outer area times `150000 (K + 1) n² δ⁴ δ^(-η)`, whenever `5 ≤ 2^K δ`.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib grainFib_mono)

/-- The projection of the frozen statement. -/
def proj (f : ℝ → ℝ) (E : Set Space) : Set (ℝ × ℝ) :=
  (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E

/-- The convex count of the frozen statement. -/
def CountF (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

/-- The total length of the height sets of a fixed tube with all others. -/
lemma sum_volume_Zset_le {η δ : ℝ} (hδ : 0 < δ) {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1) (hF : CountF η δ n x v)
    {c : ℝ} (hc : 100 < |c|) (K : ℕ) (hK : 5 ≤ 2 ^ K * δ) (i : Fin n) :
    ∑ j, (volume (Zset c (27 * δ) (x i) (v i) (x j) (v j))).toReal ≤
      (K + 1) * ((δ ^ (-η) * n * 8) *
        (4 * (27 * δ) * (27 * δ + 4 * δ) / δ + 8 * (27 * δ))) := by
  classical
  have hD : 0 ≤ δ ^ (-η) * n * 8 := by positivity
  apply dyadic_sum_le Finset.univ
    (fun j => (volume (Zset c (27 * δ) (x i) (v i) (x j) (v j))).toReal)
    (fun j => slX c (v i) - slX c (v j))
    (fun j => (Zset c (27 * δ) (x i) (v i) (x j) (v j)).Nonempty)
    hδ (by linarith) hD K
  · intro j _
    exact ENNReal.toReal_nonneg
  · intro j _
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (volume_Zset_le_two _ _ _ _ _ _)
  · intro j _ hB
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_Zset_le_div (κ := 27 * δ)
      (x := x i) (x' := x j) hB)
    have hB0 : 0 < |slX c (v i) - slX c (v j)| := abs_pos.mpr hB
    rwa [le_div_iff₀ hB0] at h
  · intro j _ hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp only [hne, measure_empty, ENNReal.toReal_zero]
  · intro j _
    have h1 := abs_slX_le hc (hv i) (hv2 i)
    have h2 := abs_slX_le hc (hv j) (hv2 j)
    calc |slX c (v i) - slX c (v j)| ≤ |slX c (v i)| + |slX c (v j)| := abs_sub _ _
      _ ≤ 2 ^ K * δ := by linarith
  · intro k
    have hρ : 0 ≤ 27 * δ + 2 * (2 ^ k * δ) + 4 * δ := by positivity
    have h := card_le_of_subset_slabW hF hδ hρ
      (Finset.univ.filter (fun j => (Zset c (27 * δ) (x i) (v i) (x j) (v j)).Nonempty ∧
        |slX c (v i) - slX c (v j)| ≤ 2 ^ k * δ))
      (c := c) (α := icX c (x i) (v i)) (β := slX c (v i)) (by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact tube_subset_slabW hδ hc (hv j) (hv2 j) (hT j) hj.2.1 hj.2.2)
    calc _ ≤ δ ^ (-η) * n * (8 * (27 * δ + 2 * (2 ^ k * δ) + 4 * δ)) := h
      _ = δ ^ (-η) * n * 8 * (27 * δ + 2 * (2 ^ k * δ) + 4 * δ) := by ring

/-- The fibre-length and strip constants combine to at most `5 δ³`. -/
lemma fibre_strip_const_le {δ C : ℝ} (hδ : 0 < δ) (hC : 100 < C) :
    (6 * δ / (C - 2)) ^ 2 * (2 * (3 * δ * (C + 3))) ≤ 5 * δ ^ 3 := by
  have hC2 : 0 < C - 2 := by linarith
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hpos : 0 < δ ^ 3 := by positivity
  have h1 : 216 * (C + 3) ≤ 5 * (C - 2) ^ 2 := by nlinarith
  nlinarith

/-- The core estimate. -/
theorem core_estimate {η δ : ℝ} (hδ : 0 < δ) {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1) (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|) (hF : CountF η δ n x v)
    {f : ℝ → ℝ} (hf : SlopeN f) (hc : 100 < |f 0|) (hδc : 1 ≤ δ * (f 0) ^ 2)
    (K : ℕ) (hK : 5 ≤ 2 ^ K * δ) :
    (∑ i, volume (Y i)) ^ 2 ≤ volume (proj f (⋃ i, Y i)) *
      ENNReal.ofReal (150000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η)) := by
  set c := f 0 with hcdef
  have hfc : Continuous f := hf.continuous
  set A := toMeasurable volume (proj f (⋃ i, Y i)) with hAdef
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAvol : volume A = volume (proj f (⋃ i, Y i)) := measure_toMeasurable _
  set H : ℝ × ℝ → ℝ≥0∞ := fun q => ∑ i, fib f (Y i) q with hHdef
  have hHm : Measurable H := Finset.measurable_sum _ (fun i _ => measurable_fib hfc (hYm i))
  have hmass : ∑ i, volume (Y i) = ∫⁻ q, H q := by
    rw [hHdef, lintegral_finsetSum _ (fun i _ => measurable_fib hfc (hYm i))]
    exact Finset.sum_congr rfl fun i _ => volume_eq_lintegral_fib hfc (hYm i)
  have hsupp : ∀ q, q ∉ A → H q = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro i _
    apply fib_eq_zero_of_notMem
    intro hqi
    apply hq
    apply subset_toMeasurable
    exact image_mono (subset_iUnion Y i) hqi
  have hCS := sq_lintegral_le_of_support volume hAm hHm hsupp
  -- fibre lengths
  set ℓ := 6 * δ / (|c| - 2) with hℓdef
  set w := 3 * δ * (|c| + 3) with hwdef
  have hℓ0 : 0 ≤ ℓ := div_nonneg (by positivity) (by linarith)
  have hfib : ∀ i u z, volume (grainFib f (Y i) u z) ≤ ENNReal.ofReal ℓ := by
    intro i u z
    by_cases hne : (grainFib f (tube δ (x i) (v i)) u z).Nonempty
    · have hz := abs_lt_one_of_grainFib (hT i) hne
      have hfz : |f z - c| ≤ 2 := hf.sub_le hz.le
      have hm : |c| - 2 ≤ |f z| := by
        have := abs_sub_abs_le_abs_sub c (f z)
        rw [abs_sub_comm] at this
        linarith
      exact (measure_mono (grainFib_mono (hYT i) u z)).trans
        (volume_grainFib_tube_le (hv i) (hv2 i) (by linarith) hm)
    · rw [not_nonempty_iff_eq_empty] at hne
      have h0 : grainFib f (Y i) u z = ∅ :=
        subset_empty_iff.mp (hne ▸ grainFib_mono (hYT i) u z)
      rw [h0, measure_empty]
      exact zero_le
  have hpair : ∀ i j, ∫⁻ q, fib f (Y i) q * fib f (Y j) q ≤
      ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * volume (Zset c (27 * δ) (x i) (v i) (x j) (v j)) := by
    intro i j
    apply lintegral_fib_mul_le hfc (hYm i) (hYm j) hℓ0 (hfib i) (hfib j)
      (φ := ctr f (x i) (v i))
    intro u z hi hj
    exact mem_Zset_of_grainFib hδ hf hc hδc (hv i) (hv2 i) (hT i) (hv j) (hv2 j) (hT j)
      (hi.mono (grainFib_mono (hYT i) u z)) (hj.mono (grainFib_mono (hYT j) u z))
  -- the energy
  set R := (K + 1) * ((δ ^ (-η) * n * 8) *
        (4 * (27 * δ) * (27 * δ + 4 * δ) / δ + 8 * (27 * δ))) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hrow : ∀ i, ∑ j, volume (Zset c (27 * δ) (x i) (v i) (x j) (v j)) ≤ ENNReal.ofReal R := by
    intro i
    have hfin : ∀ j ∈ Finset.univ,
        volume (Zset c (27 * δ) (x i) (v i) (x j) (v j)) ≠ ⊤ := fun j _ =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_Zset_le_two _ _ _ _ _ _)
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.mpr hfin) hR0,
      ENNReal.toReal_sum hfin]
    exact sum_volume_Zset_le hδ hv hv2 hT hF hc K hK i
  have hE : ∫⁻ q, H q ^ 2 ≤
      ENNReal.ofReal (150000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η)) := by
    rw [hHdef, lintegral_sum_fib_sq hfc hYm]
    calc ∑ i, ∑ j, ∫⁻ q, fib f (Y i) q * fib f (Y j) q
        ≤ ∑ i, ∑ j, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
            volume (Zset c (27 * δ) (x i) (v i) (x j) (v j)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = ∑ i, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
            ∑ j, volume (Zset c (27 * δ) (x i) (v i) (x j) (v j)) := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * ENNReal.ofReal R := by
          gcongr with i
          exact hrow i
      _ = ENNReal.ofReal (n * (ℓ ^ 2 * (2 * w) * R)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (150000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η)) := by
          apply ENNReal.ofReal_le_ofReal
          have hc5 := fibre_strip_const_le hδ hc
          have hδη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
          have hRval : R = (K + 1) * δ ^ (-η) * n * (28512 * δ) := by
            rw [hRdef]
            field_simp
            ring
          rw [hRval]
          have hK0 : (0 : ℝ) ≤ K + 1 := by positivity
          have hX : 0 ≤ (K + 1) * δ ^ (-η) * n * (28512 * δ) := by positivity
          calc (n : ℝ) * (ℓ ^ 2 * (2 * w) * ((K + 1) * δ ^ (-η) * n * (28512 * δ)))
              ≤ n * (5 * δ ^ 3 * ((K + 1) * δ ^ (-η) * n * (28512 * δ))) := by
                gcongr
            _ = 142560 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η) := by ring
            _ ≤ 150000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η) := by
                gcongr
                norm_num
  calc (∑ i, volume (Y i)) ^ 2 = (∫⁻ q, H q) ^ 2 := by rw [hmass]
    _ ≤ volume A * ∫⁻ q, H q ^ 2 := hCS
    _ ≤ volume (proj f (⋃ i, Y i)) *
          ENNReal.ofReal (150000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-η)) := by
        rw [hAvol]
        gcongr

end WangZahlLot.Obl.wz_small_twist_projection_estimate
