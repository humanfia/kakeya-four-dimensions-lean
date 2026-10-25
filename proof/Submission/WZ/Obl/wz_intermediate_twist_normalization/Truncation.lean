-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Truncation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Classes
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Slice

/-!
# The truncated energy

`clW k` is the near multiplicity of the enlarged class `k`: the sum of the fibre lengths of the
shadings of its tubes. The truncated shadings `trY λ i` keep the part of `Y i` lying over the
points where the near multiplicity of the class of `i` is at most `λ`. For them the energy
splits into near pairs, bounded by `λ` times the mass, and far pairs, bounded by the far rows:

  `(∑ |trY i|)² ≤ |P_f(⋃ Y)| · (λ ∑ |trY i| + n · 5 δ³ R_far)`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj CountF fib
  measurable_fib volume_eq_lintegral_fib lintegral_fib_mul_le lintegral_sum_fib_sq
  sq_lintegral_le_of_support fib_eq_zero_of_notMem slX ctr fibre_strip_const_le
  volume_Zset_le_two)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (grainFib grainFib_mono)

/-- The near multiplicity of an enlarged class. -/
noncomputable def clW {n : ℕ} (f : ℝ → ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (k : ℤ × ℤ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ j ∈ clSet (f 0) x v k, fib f (Y j) q

/-- Where the near multiplicity of the class of a tube is at most `λ`. -/
def lowSet {n : ℕ} (f : ℝ → ℝ) (lam : ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (k : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {q | clW f x v Y k q ≤ ENNReal.ofReal lam}

/-- Where the near multiplicity of a class exceeds `λ`. -/
def clG {n : ℕ} (f : ℝ → ℝ) (lam : ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (k : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {q | ENNReal.ofReal lam < clW f x v Y k q}

/-- The truncated shadings. -/
def trY {n : ℕ} (f : ℝ → ℝ) (lam : ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (i : Fin n) : Set Space :=
  Y i ∩ pmap f ⁻¹' lowSet f lam x v Y (clIdx (f 0) (x i) (v i))

section

variable {n : ℕ} {f : ℝ → ℝ} {x v : Fin n → Space} {Y : Fin n → Set Space}

theorem measurable_clW (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (k : ℤ × ℤ) :
    Measurable (clW f x v Y k) :=
  Finset.measurable_sum _ fun j _ => measurable_fib hf (hYm j)

theorem measurableSet_lowSet (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (lam : ℝ)
    (k : ℤ × ℤ) : MeasurableSet (lowSet f lam x v Y k) :=
  measurableSet_le (measurable_clW hf hYm k) measurable_const

theorem measurableSet_clG (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (lam : ℝ)
    (k : ℤ × ℤ) : MeasurableSet (clG f lam x v Y k) :=
  measurableSet_lt measurable_const (measurable_clW hf hYm k)

theorem measurableSet_trY (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (lam : ℝ)
    (i : Fin n) : MeasurableSet (trY f lam x v Y i) :=
  (hYm i).inter ((measurableSet_lowSet hf hYm lam _).preimage (continuous_pmap hf).measurable)

theorem compl_lowSet (lam : ℝ) (k : ℤ × ℤ) :
    (lowSet f lam x v Y k)ᶜ = clG f lam x v Y k := by
  ext q
  simp [lowSet, clG, not_le]

/-- **The truncated energy.** -/
theorem trunc_energy {η δ : ℝ} (hδ : 0 < δ) (hv : ∀ i, ‖v i‖ = 1)
    (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|) (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hF : CountF η δ n x v) (hf : SlopeN f) (hc : 100 < |f 0|) (hδc : δ * (f 0) ^ 2 ≤ 1)
    (K : ℕ) (hK : 5 ≤ 2 ^ K * (100 / (f 0) ^ 2)) (lam : ℝ) :
    (∑ i, volume (trY f lam x v Y i)) ^ 2 ≤ volume (proj f (⋃ i, Y i)) *
      (ENNReal.ofReal lam * ∑ i, volume (trY f lam x v Y i) +
        ENNReal.ofReal (n * (5 * δ ^ 3 *
          ((K + 1) * (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)))))) := by
  classical
  set c := f 0 with hcdef
  have hfc : Continuous f := hf.continuous
  set Y' := trY f lam x v Y with hY'def
  have hY'm : ∀ i, MeasurableSet (Y' i) := fun i => measurableSet_trY hfc hYm lam i
  have hY'Y : ∀ i, Y' i ⊆ Y i := fun i => inter_subset_left
  have hY'T : ∀ i, Y' i ⊆ tube δ (x i) (v i) := fun i => (hY'Y i).trans (hYT i)
  set A := toMeasurable volume (proj f (⋃ i, Y' i)) with hAdef
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hAvol : volume A = volume (proj f (⋃ i, Y' i)) := measure_toMeasurable _
  set H : ℝ × ℝ → ℝ≥0∞ := fun q => ∑ i, fib f (Y' i) q with hHdef
  have hHm : Measurable H := Finset.measurable_sum _ (fun i _ => measurable_fib hfc (hY'm i))
  have hmass : ∑ i, volume (Y' i) = ∫⁻ q, H q := by
    rw [hHdef, lintegral_finsetSum _ (fun i _ => measurable_fib hfc (hY'm i))]
    exact Finset.sum_congr rfl fun i _ => volume_eq_lintegral_fib hfc (hY'm i)
  have hsupp : ∀ q, q ∉ A → H q = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro i _
    apply fib_eq_zero_of_notMem
    intro hqi
    apply hq
    apply subset_toMeasurable
    exact image_mono (subset_iUnion Y' i) hqi
  have hCS := sq_lintegral_le_of_support volume hAm hHm hsupp
  -- fibre lengths
  set ℓ := 6 * δ / (|c| - 2) with hℓdef
  set w := 3 * δ * (|c| + 3) with hwdef
  have hℓ0 : 0 ≤ ℓ := div_nonneg (by positivity) (by linarith)
  have hfib : ∀ i u z, volume (grainFib f (Y' i) u z) ≤ ENNReal.ofReal ℓ := fun i u z =>
    volume_grainFib_le_of_subset hf hc (hv i) (hv2 i) (hT i) (hY'T i) u z
  have hpair : ∀ i j, ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q ≤
      ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * volume (Z2 f δ (x i) (v i) (x j) (v j)) := by
    intro i j
    apply lintegral_fib_mul_le hfc (hY'm i) (hY'm j) hℓ0 (hfib i) (hfib j)
      (φ := ctr f (x i) (v i))
    intro u z hi hj
    exact pair_support_Z2 hf (hv i) (hv2 i) (hT i) (hv j) (hv2 j)
      (hi.mono (grainFib_mono (hY'T i) u z)) (hj.mono (grainFib_mono (hY'T j) u z))
  -- far rows
  set Rf := ((K : ℝ) + 1) * (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)) with hRf
  have hRf0 : 0 ≤ Rf := by positivity
  set far : Fin n → Finset (Fin n) := fun i =>
    Finset.univ.filter (fun j => 100 / c ^ 2 ≤ |slX c (v i) - slX c (v j)|) with hfar
  have hrow : ∀ i, ∑ j ∈ far i, volume (Z2 f δ (x i) (v i) (x j) (v j)) ≤ ENNReal.ofReal Rf := by
    intro i
    have hfin : ∀ j ∈ far i, volume (Z2 f δ (x i) (v i) (x j) (v j)) ≠ ⊤ := by
      intro j _
      refine ne_top_of_le_ne_top (measure_ne_top_of_subset (s := Icc (-1 : ℝ) 1) ?_ ?_) le_rfl
      · intro z hz; exact hz.1
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.mpr hfin) hRf0,
      ENNReal.toReal_sum hfin]
    exact far_row_bound hδ hv hv2 hT hF hf hc hδc K hK i
  have hfar_le : ∀ i, ∑ j ∈ far i, ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q ≤
      ENNReal.ofReal (5 * δ ^ 3 * Rf) := by
    intro i
    calc ∑ j ∈ far i, ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q
        ≤ ∑ j ∈ far i, ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
            volume (Z2 f δ (x i) (v i) (x j) (v j)) := Finset.sum_le_sum fun j _ => hpair i j
      _ = ENNReal.ofReal (ℓ ^ 2 * (2 * w)) *
            ∑ j ∈ far i, volume (Z2 f δ (x i) (v i) (x j) (v j)) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * ENNReal.ofReal Rf := by gcongr; exact hrow i
      _ ≤ ENNReal.ofReal (5 * δ ^ 3) * ENNReal.ofReal Rf :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (fibre_strip_const_le hδ hc)) _
      _ = ENNReal.ofReal (5 * δ ^ 3 * Rf) := (ENNReal.ofReal_mul (by positivity)).symm
  -- near pairs
  have hnear_pt : ∀ i q, ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ far i),
      fib f (Y' i) q * fib f (Y' j) q ≤ ENNReal.ofReal lam * fib f (Y' i) q := by
    intro i q
    set S := Finset.univ.filter (fun j => ¬ j ∈ far i)
    set T := clSet c x v (clIdx c (x i) (v i))
    have h1 : ∀ j ∈ S, fib f (Y' i) q * fib f (Y' j) q ≤
        if j ∈ T then fib f (Y' i) q * fib f (Y j) q else 0 := by
      intro j hj
      split_ifs with hjT
      · gcongr
        exact measure_mono (grainFib_mono (hY'Y j) q.1 q.2)
      · -- a near pair outside the enlarged class has disjoint fibres
        by_contra hpos
        push Not at hpos
        have hne : ∀ k, fib f (Y' k) q ≠ 0 → (grainFib f (tube δ (x k) (v k)) q.1 q.2).Nonempty := by
          intro k hk
          by_contra he
          rw [Set.not_nonempty_iff_eq_empty] at he
          apply hk
          have : grainFib f (Y' k) q.1 q.2 = ∅ :=
            subset_empty_iff.mp (he ▸ grainFib_mono (hY'T k) q.1 q.2)
          simp [fib, this]
        have hi0 : fib f (Y' i) q ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
        have hj0 : fib f (Y' j) q ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
        have hZ := pair_support_Z2 hf (hv i) (hv2 i) (hT i) (hv j) (hv2 j) (hne i hi0) (hne j hj0)
        have hjfar : ¬ (100 / c ^ 2 ≤ |slX c (v i) - slX c (v j)|) := by
          have := (Finset.mem_filter.mp hj).2
          simpa [hfar] using this
        push Not at hjfar
        exact hjT (mem_clSet_of_near hδ hf hc hδc hv hv2 hT ⟨q.2, hZ.1⟩ hjfar)
    calc ∑ j ∈ S, fib f (Y' i) q * fib f (Y' j) q
        ≤ ∑ j ∈ S, (if j ∈ T then fib f (Y' i) q * fib f (Y j) q else 0) :=
          Finset.sum_le_sum h1
      _ = ∑ j ∈ S.filter (fun j => j ∈ T), fib f (Y' i) q * fib f (Y j) q :=
          (Finset.sum_filter (s := S) (p := fun j => j ∈ T)
            (fun j => fib f (Y' i) q * fib f (Y j) q)).symm
      _ ≤ ∑ j ∈ T, fib f (Y' i) q * fib f (Y j) q := by
          apply Finset.sum_le_sum_of_subset
          intro j hj
          exact (Finset.mem_filter.mp hj).2
      _ = fib f (Y' i) q * clW f x v Y (clIdx c (x i) (v i)) q := by
          rw [clW, Finset.mul_sum]
      _ ≤ ENNReal.ofReal lam * fib f (Y' i) q := by
          rw [hY'def, trY, fib_inter_pmap_preimage]
          by_cases hq : q ∈ lowSet f lam x v Y (clIdx c (x i) (v i))
          · rw [indicator_of_mem hq, mul_comm]
            have hq' : clW f x v Y (clIdx c (x i) (v i)) q ≤ ENNReal.ofReal lam := hq
            gcongr
          · rw [indicator_of_notMem hq, zero_mul, mul_zero]
  have hnear : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ far i),
      ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q ≤ ENNReal.ofReal lam * volume (Y' i) := by
    intro i
    have hsum_int : ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ far i),
        ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q =
        ∫⁻ q, ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ far i),
          fib f (Y' i) q * fib f (Y' j) q :=
      (lintegral_finsetSum (Finset.univ.filter (fun j => ¬ j ∈ far i))
        (f := fun j q => fib f (Y' i) q * fib f (Y' j) q)
        (fun j _ => (measurable_fib hfc (hY'm i)).mul (measurable_fib hfc (hY'm j)))).symm
    rw [hsum_int, volume_eq_lintegral_fib hfc (hY'm i),
      ← lintegral_const_mul _ (measurable_fib hfc (hY'm i))]
    exact lintegral_mono fun q => hnear_pt i q
  -- the energy
  have hE : ∫⁻ q, H q ^ 2 ≤ ENNReal.ofReal lam * ∑ i, volume (Y' i) +
      ENNReal.ofReal (n * (5 * δ ^ 3 * Rf)) := by
    rw [hHdef, lintegral_sum_fib_sq hfc hY'm]
    calc ∑ i, ∑ j, ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q
        = ∑ i, ((∑ j ∈ far i, ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q) +
            ∑ j ∈ Finset.univ.filter (fun j => ¬ j ∈ far i),
              ∫⁻ q, fib f (Y' i) q * fib f (Y' j) q) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ far i)]
          congr 1
          refine Finset.sum_congr ?_ fun j _ => rfl
          ext j
          simp [hfar]
      _ ≤ ∑ i, (ENNReal.ofReal (5 * δ ^ 3 * Rf) + ENNReal.ofReal lam * volume (Y' i)) :=
          Finset.sum_le_sum fun i _ => add_le_add (hfar_le i) (hnear i)
      _ = ENNReal.ofReal lam * ∑ i, volume (Y' i) + ENNReal.ofReal (n * (5 * δ ^ 3 * Rf)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum, add_comm]
          congr 1
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  calc (∑ i, volume (Y' i)) ^ 2 = (∫⁻ q, H q) ^ 2 := by rw [hmass]
    _ ≤ volume A * ∫⁻ q, H q ^ 2 := hCS
    _ ≤ volume (proj f (⋃ i, Y i)) *
          (ENNReal.ofReal lam * ∑ i, volume (Y' i) + ENNReal.ofReal (n * (5 * δ ^ 3 * Rf))) := by
        rw [hAvol]
        gcongr
        exact image_mono (iUnion_mono hY'Y)

end

end WangZahlLot.Obl.wz_intermediate_twist_normalization
