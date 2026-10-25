-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Energy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Fibre

/-!
# The fibre-length energy

`fib f A q = volume (grainFib f A q.1 q.2)` is the length of the grain fibre of `A` over the
projected point `q = (u, z)`.  Its integral is `volume A`, it vanishes off the projection of
`A`, and the Cauchy–Schwarz inequality bounds the square of the total mass by the projected
area times the energy `∫⁻ (∑ fib)²`.  Pairwise energies are bounded by fibre length and the
set of heights where both fibres can be nonempty.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib mem_grainFib ofTwist_zero
  ofTwist_one ofTwist_two measurable_grainFib_volume volume_eq_lintegral_grainFib)

/-- The fibre length over a projected point. -/
noncomputable def fib (f : ℝ → ℝ) (A : Set Space) (q : ℝ × ℝ) : ℝ≥0∞ :=
  volume (grainFib f A q.1 q.2)

lemma measurable_fib {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space} (hA : MeasurableSet A) :
    Measurable (fib f A) :=
  measurable_grainFib_volume hf hA

lemma volume_eq_lintegral_fib {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hA : MeasurableSet A) : volume A = ∫⁻ q, fib f A q := by
  rw [volume_eq_lintegral_grainFib hf hA, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (measurable_fib hf hA)]
  rfl

/-- The fibre length vanishes off the projection. -/
lemma fib_eq_zero_of_notMem {f : ℝ → ℝ} {A : Set Space} {q : ℝ × ℝ}
    (hq : q ∉ (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' A) : fib f A q = 0 := by
  have hempty : grainFib f A q.1 q.2 = ∅ := by
    ext y
    simp only [mem_empty_iff_false, iff_false]
    intro hy
    apply hq
    refine ⟨ofTwist f q.1 y q.2, hy, ?_⟩
    simp only [ofTwist_zero, ofTwist_one, ofTwist_two]
    ext <;> simp
  simp [fib, hempty]

/-- Cauchy–Schwarz for a function supported in a measurable set. -/
lemma sq_lintegral_le_of_support {α : Type*} [MeasurableSpace α] (μ : Measure α) {A : Set α}
    (hA : MeasurableSet A) {H : α → ℝ≥0∞} (hH : Measurable H) (hsupp : ∀ q, q ∉ A → H q = 0) :
    (∫⁻ q, H q ∂μ) ^ 2 ≤ μ A * ∫⁻ q, H q ^ 2 ∂μ := by
  set g : α → ℝ≥0∞ := A.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator hA
  have h1 : ∫⁻ q, H q ∂μ = ∫⁻ q, (g * H) q ∂μ := by
    congr 1
    funext q
    by_cases hq : q ∈ A
    · simp [hg, hq]
    · simp [hg, hq, hsupp q hq]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hgm.aemeasurable hH.aemeasurable
  have h2 : ∫⁻ q, g q ^ (2 : ℝ) ∂μ = μ A := by
    rw [← lintegral_indicator_one hA]
    congr 1
    funext q
    by_cases hq : q ∈ A
    · simp [hg, hq]
    · simp [hg, hq]
  have h3 : ∫⁻ q, H q ^ (2 : ℝ) ∂μ = ∫⁻ q, H q ^ 2 ∂μ := by
    congr 1
    funext q
    exact ENNReal.rpow_two (H q)
  rw [h2, h3] at hHolder
  rw [h1]
  calc (∫⁻ q, (g * H) q ∂μ) ^ 2
      ≤ ((μ A) ^ (1 / 2 : ℝ) * (∫⁻ q, H q ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = μ A * ∫⁻ q, H q ^ 2 ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

/-- The pairwise energy is controlled by the fibre length and the heights where both fibres
can be nonempty. -/
lemma lintegral_fib_mul_le {f : ℝ → ℝ} (hf : Continuous f) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {Z : Set ℝ} {ℓ w : ℝ} (hℓ : 0 ≤ ℓ)
    {φ : ℝ → ℝ}
    (hfibA : ∀ u z, volume (grainFib f A u z) ≤ ENNReal.ofReal ℓ)
    (hfibB : ∀ u z, volume (grainFib f B u z) ≤ ENNReal.ofReal ℓ)
    (hloc : ∀ u z, (grainFib f A u z).Nonempty → (grainFib f B u z).Nonempty →
      z ∈ Z ∧ |u - φ z| ≤ w) :
    ∫⁻ q, fib f A q * fib f B q ≤ ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * volume Z := by
  have hmeas : Measurable (fun q => fib f A q * fib f B q) :=
    (measurable_fib hf hA).mul (measurable_fib hf hB)
  rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hmeas]
  have hzero : ∀ u z, ¬ ((grainFib f A u z).Nonempty ∧ (grainFib f B u z).Nonempty) →
      fib f A (u, z) * fib f B (u, z) = 0 := by
    intro u z h
    rw [not_and_or] at h
    rcases h with h | h
    · rw [not_nonempty_iff_eq_empty] at h
      simp [fib, h]
    · rw [not_nonempty_iff_eq_empty] at h
      simp [fib, h]
  calc ∫⁻ z, ∫⁻ u, fib f A (u, z) * fib f B (u, z)
      ≤ ∫⁻ z, Z.indicator (fun _ => ENNReal.ofReal (ℓ ^ 2 * (2 * w))) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ Z
        · rw [indicator_of_mem hz]
          calc ∫⁻ u, fib f A (u, z) * fib f B (u, z)
              ≤ ∫⁻ u, (closedBall (φ z) w).indicator (fun _ => ENNReal.ofReal (ℓ ^ 2)) u := by
                refine lintegral_mono fun u => ?_
                by_cases hboth : (grainFib f A u z).Nonempty ∧ (grainFib f B u z).Nonempty
                · have hu : u ∈ closedBall (φ z) w := by
                    rw [mem_closedBall, Real.dist_eq]
                    exact (hloc u z hboth.1 hboth.2).2
                  rw [indicator_of_mem hu]
                  calc fib f A (u, z) * fib f B (u, z)
                      ≤ ENNReal.ofReal ℓ * ENNReal.ofReal ℓ := mul_le_mul' (hfibA u z) (hfibB u z)
                    _ = ENNReal.ofReal (ℓ ^ 2) := by rw [← ENNReal.ofReal_mul hℓ, sq]
                · rw [hzero u z hboth]
                  exact zero_le
            _ = ENNReal.ofReal (ℓ ^ 2) * volume (closedBall (φ z) w) :=
                lintegral_indicator_const measurableSet_closedBall _
            _ = ENNReal.ofReal (ℓ ^ 2 * (2 * w)) := by
                rw [Real.volume_closedBall, ← ENNReal.ofReal_mul (by positivity)]
        · rw [indicator_of_notMem hz]
          have h0 : ∀ u, fib f A (u, z) * fib f B (u, z) = 0 := by
            intro u
            apply hzero u z
            rintro ⟨h1, h2⟩
            exact hz (hloc u z h1 h2).1
          simp [h0]
    _ ≤ ENNReal.ofReal (ℓ ^ 2 * (2 * w)) * volume Z := lintegral_indicator_const_le _ _

/-- The energy of a sum of fibre lengths expands into pairwise energies. -/
lemma lintegral_sum_fib_sq {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) :
    ∫⁻ q, (∑ i, fib f (Y i) q) ^ 2 = ∑ i, ∑ j, ∫⁻ q, fib f (Y i) q * fib f (Y j) q := by
  have hexp : ∀ q, (∑ i, fib f (Y i) q) ^ 2 = ∑ i, ∑ j, fib f (Y i) q * fib f (Y j) q := by
    intro q
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hm : ∀ i j, Measurable (fun q => fib f (Y i) q * fib f (Y j) q) := fun i j =>
    (measurable_fib hf (hY i)).mul (measurable_fib hf (hY j))
  rw [lintegral_finsetSum Finset.univ
    (f := fun i q => ∑ j, fib f (Y i) q * fib f (Y j) q)
    (fun i _ => Finset.measurable_sum Finset.univ (fun j _ => hm i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_finsetSum Finset.univ (f := fun j q => fib f (Y i) q * fib f (Y j) q)
    (fun j _ => hm i j)

end WangZahlLot.Obl.wz_small_twist_projection_estimate
