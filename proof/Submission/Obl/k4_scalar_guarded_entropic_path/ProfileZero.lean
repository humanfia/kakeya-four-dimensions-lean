/- Adapted from same-tree o168/x0569-o196port, commit c22aeb8a. -/
/-
Adapted from: here:o168 (session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/ProfileZero.lean), renamed into the o196
namespace. Its own provenance comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Guard

/-!
# The absolute density profile of an exact problem is nonpositive at depth zero

At depth zero the observation bins have unit width. Almost every incidence has time in
`[0, 1]` and coefficients bounded by `K`, so the pushed-forward incidence law lives on a
region of reference volume `O(K ^ 3)`. Typical densities are `N ^ (-f 0 ± τ)` off a
power-small exceptional mass, while the weighted total mass is at least `1 / K`. Since
`K` is subpower, `f 0 > 0` is impossible.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

/-- A density bound: the mass of the points where the density is at most `M` is at most
`M` times the reference measure of any region carrying the pushed-forward law. -/
theorem measure_density_le_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (Φ : X → Y) (hΦ : Measurable Φ)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (hmap : μ.map Φ = ν.withDensity g)
    (A : Set Y) (hA : MeasurableSet A) (hconc : μ (Φ ⁻¹' Aᶜ) = 0) (M : ℝ≥0∞) :
    μ {x | g (Φ x) ≤ M} ≤ M * ν A := by
  have hset : MeasurableSet {y | g y ≤ M} := measurableSet_le hg measurable_const
  have h1 : μ {x | g (Φ x) ≤ M} = (μ.map Φ) {y | g y ≤ M} := by
    rw [Measure.map_apply hΦ hset]; rfl
  have h2 : (μ.map Φ) {y | g y ≤ M} ≤ (μ.map Φ) ({y | g y ≤ M} ∩ A) + (μ.map Φ) Aᶜ := by
    calc (μ.map Φ) {y | g y ≤ M}
        ≤ (μ.map Φ) (({y | g y ≤ M} ∩ A) ∪ Aᶜ) := by
          apply measure_mono
          intro y hy
          by_cases hyA : y ∈ A
          · exact Or.inl ⟨hy, hyA⟩
          · exact Or.inr hyA
      _ ≤ _ := measure_union_le _ _
  have h3 : (μ.map Φ) Aᶜ = 0 := by
    rw [Measure.map_apply hΦ hA.compl]; exact hconc
  have h4 : (μ.map Φ) ({y | g y ≤ M} ∩ A) ≤ M * ν A := by
    rw [hmap, withDensity_apply _ (hset.inter hA)]
    calc ∫⁻ y in {y | g y ≤ M} ∩ A, g y ∂ν
        ≤ ∫⁻ _ in {y | g y ≤ M} ∩ A, M ∂ν := by
          apply setLIntegral_mono measurable_const
          intro y hy; exact hy.1
      _ = M * ν ({y | g y ≤ M} ∩ A) := by rw [setLIntegral_const]
      _ ≤ M * ν A := by gcongr; exact inter_subset_right
  rw [h1]
  calc _ ≤ (μ.map Φ) ({y | g y ≤ M} ∩ A) + (μ.map Φ) Aᶜ := h2
    _ ≤ M * ν A + 0 := by rw [h3]; exact add_le_add h4 le_rfl
    _ = M * ν A := add_zero _

/-- The observation map at depth `r`. -/
abbrev obsMap (N r : ℝ) (z : Incidence) : (Fin 2 → ℝ) × ℤ :=
  ((![z.2, Split.y z.1 z.2] : Fin 2 → ℝ), (⌊Split.x z.1 z.2 / (N ^ (-r))⌋ : ℤ))

/-- The region carrying the depth-zero observations of incidences with time in
`[0, 1]` and coefficients bounded by `K`. -/
def zeroRegion (K : ℝ) : Set ((Fin 2 → ℝ) × ℤ) :=
  (Set.univ.pi fun _ : Fin 2 => Icc (-(2 * K)) (2 * K)) ×ˢ
    ((Finset.Icc (-(⌈3 * K⌉ + 1)) (⌈3 * K⌉ + 1) : Finset ℤ) : Set ℤ)

theorem measurableSet_zeroRegion (K : ℝ) : MeasurableSet (zeroRegion K) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod (Set.toFinite _).measurableSet

theorem obsMap_mem_zeroRegion {N K : ℝ} (hK1 : 1 ≤ K) {z : Incidence}
    (ht : z.2 ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |z.1.2 e| ≤ K) :
    obsMap N 0 z ∈ zeroRegion K := by
  have hK : 0 ≤ K := by linarith
  obtain ⟨ht0, ht1⟩ := ht
  have hy : |Split.y z.1 z.2| ≤ 2 * K := by
    have h0 := hl 0
    have h1 := hl 1
    have : |z.2 * z.1.2 1| ≤ K := by
      rw [abs_mul, abs_of_nonneg ht0]
      nlinarith [abs_nonneg (z.1.2 1)]
    calc |Split.y z.1 z.2| = |z.1.2 0 + z.2 * z.1.2 1| := rfl
      _ ≤ |z.1.2 0| + |z.2 * z.1.2 1| := abs_add_le _ _
      _ ≤ 2 * K := by linarith
  have hx : |Split.x z.1 z.2| ≤ 3 * K := by
    have h2 := hl 2
    have h3 := hl 3
    have h4 := hl 4
    have hA : |z.2 * z.1.2 3| ≤ K := by
      rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (z.1.2 3)]
    have hB : |z.2 ^ 2 * z.1.2 4| ≤ K := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have : z.2 ^ 2 ≤ 1 := by nlinarith
      nlinarith [abs_nonneg (z.1.2 4)]
    calc |Split.x z.1 z.2| = |z.1.2 2 + z.2 * z.1.2 3 + z.2 ^ 2 * z.1.2 4| := rfl
      _ ≤ |z.1.2 2 + z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := abs_add_le _ _
      _ ≤ |z.1.2 2| + |z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 3 * K := by linarith
  refine ⟨?_, ?_⟩
  · intro i _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mem_Icc]
      constructor <;> linarith
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact abs_le.mp hy
  · simp only [Finset.coe_Icc, mem_Icc]
    have hdiv : Split.x z.1 z.2 / (N ^ (-(0 : ℝ))) = Split.x z.1 z.2 := by
      simp
    rw [hdiv]
    have hxl := (abs_le.mp hx).1
    have hxu := (abs_le.mp hx).2
    have hc : (3 * K : ℝ) ≤ ⌈3 * K⌉ := Int.le_ceil _
    constructor
    · have : ((-(⌈3 * K⌉ + 1) : ℤ) : ℝ) ≤ ⌊Split.x z.1 z.2⌋ := by
        have := Int.sub_one_lt_floor (Split.x z.1 z.2)
        push_cast
        linarith
      exact_mod_cast this
    · have : (⌊Split.x z.1 z.2⌋ : ℝ) ≤ ((⌈3 * K⌉ + 1 : ℤ) : ℝ) := by
        have := Int.floor_le (Split.x z.1 z.2)
        push_cast
        linarith
      exact_mod_cast this

theorem zeroRegion_measure_le {K : ℝ} (hK : 1 ≤ K) :
    ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)) (zeroRegion K) ≤
      ENNReal.ofReal (200 * K ^ 3) := by
  have hK0 : 0 ≤ K := by linarith
  rw [zeroRegion, Measure.prod_prod, volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Measure.count_apply_finset, Int.card_Icc]
  have hc : (⌈3 * K⌉ : ℝ) < 3 * K + 1 := Int.ceil_lt_add_one _
  have hc0 : (0 : ℤ) ≤ ⌈3 * K⌉ := Int.ceil_nonneg (by positivity)
  have hcard : ((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1)).toNat : ℝ) ≤ 6 * K + 5 := by
    have h1 : (((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1)).toNat : ℕ) : ℤ) =
        ⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1) := Int.toNat_of_nonneg (by omega)
    have h2 : (((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1)).toNat : ℕ) : ℝ) =
        ((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1) : ℤ) : ℝ) := by
      rw [← h1]; norm_cast
    rw [h2]
    push_cast
    linarith
  have hcard' : ((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1)).toNat : ℝ≥0∞) ≤
      ENNReal.ofReal (6 * K + 5) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc ENNReal.ofReal (2 * K - -(2 * K)) ^ 2 *
        ((⌈3 * K⌉ + 1 + 1 - -(⌈3 * K⌉ + 1)).toNat : ℝ≥0∞)
      ≤ ENNReal.ofReal (4 * K) ^ 2 * ENNReal.ofReal (6 * K + 5) := by
        gcongr
        · exact le_of_eq (by ring_nf)
    _ = ENNReal.ofReal ((4 * K) ^ 2 * (6 * K + 5)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (200 * K ^ 3) := by
        apply ENNReal.ofReal_le_ofReal
        have hK2 : K ^ 2 ≤ K ^ 3 := by
          have := pow_le_pow_right₀ hK (show 2 ≤ 3 by norm_num)
          exact this
        nlinarith [sq_nonneg K]

/-- Almost every incidence of an exact problem lands in the depth-zero region. -/
theorem mu_obs_zeroRegion_compl {p : Code} (hp : Split.Exact p) (k : ℕ)
    (γ : Fin (p.1 k)) :
    Split.mu p k γ (obsMap (p.N k) 0 ⁻¹' (zeroRegion (p.K k))ᶜ) = 0 := by
  have hw := (hp.2.1 k).2.2.2.1 γ
  obtain ⟨hprob, _, hae, hEmeas, hEsub, _, _⟩ := hw
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one (hp.1.2.2.1.1 k)
  have hbad : (p.prior k γ) {l | ¬ ∀ e, |l.2 e| ≤ p.K k} = 0 := by
    rw [ae_iff] at hae
    exact hae
  -- incidences outside the region are in E with a bad coefficient
  have hsub : (obsMap (p.N k) 0 ⁻¹' (zeroRegion (p.K k))ᶜ) ∩ p.support k γ ⊆
      {l | ¬ ∀ e, |l.2 e| ≤ p.K k} ×ˢ univ := by
    rintro z ⟨hz, hzE⟩
    refine ⟨?_, mem_univ _⟩
    intro hl
    exact hz (obsMap_mem_zeroRegion (hp.1.2.2.1.1 k) (hEsub hzE).2 hl)
  have hEmeas' : MeasurableSet (p.support k γ) := hEmeas
  change ((p.prior k γ).prod volume).restrict (p.support k γ) _ = 0
  rw [Measure.restrict_apply' hEmeas']
  apply measure_mono_null hsub
  rw [Measure.prod_prod, hbad, zero_mul]

/-- **Every exact problem has nonpositive absolute profile at depth zero.** -/
theorem Exact.profile_zero_nonpos {p : Code} (hp : Split.Exact p) : p.profile 0 ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set f := p.profile 0 with hf
  have hL : 0 < p.L := exact_length_pos hp
  obtain ⟨c, hc, hev⟩ := hp.2.2.2.2.2.1 0 (f / 2) le_rfl hL.le (by positivity)
  set c' := min c (f / 4) with hc'
  have hc'pos : 0 < c' := lt_min hc (by positivity)
  have hc'le : c' ≤ c := min_le_left _ _
  have hc'f : c' ≤ f / 4 := min_le_right _ _
  have hKev : ∀ᶠ k in atTop, p.K k ≤ p.N k ^ (c' / 8) :=
    hp.1.2.2.1.2 (c' / 8) (by positivity)
  have hNlarge : ∀ᶠ k in atTop, (201 : ℝ) < p.N k ^ (7 * c' / 8) :=
    ((tendsto_rpow_atTop (by positivity)).comp hp.1.2.1).eventually_gt_atTop 201
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev.and (hKev.and hNlarge)).exists
  -- notation at the sample `k`
  set N := p.N k with hN
  set K := p.K k with hKdef
  have hN1 : 1 ≤ N := exact_N_ge_one hp k
  have hNpos : 0 < N := by linarith
  have hK1 : 1 ≤ K := hp.1.2.2.1.1 k
  have hKpos : 0 < K := by linarith
  -- the good part of each world has small mass
  have hgood : ∀ γ : Fin (p.1 k), Split.mu p k γ
      {z | p.density k γ 0 (obsMap N 0 z) ≤ ENNReal.ofReal (N ^ (-f + f / 2))} ≤
      ENNReal.ofReal (N ^ (-f + f / 2)) * ENNReal.ofReal (200 * K ^ 3) := by
    intro γ
    obtain ⟨hgm, hmap⟩ := hp.2.2.1 k γ 0 le_rfl hL.le
    have hΦ : Measurable (obsMap N 0) := by
      have hy : Measurable (fun z : Incidence => Split.y z.1 z.2) := by
        unfold Split.y; fun_prop
      have hx : Measurable (fun z : Incidence => Split.x z.1 z.2) := by
        unfold Split.x; fun_prop
      have hv : Measurable (fun z : Incidence => (![z.2, Split.y z.1 z.2] : Fin 2 → ℝ)) := by
        rw [measurable_pi_iff]
        intro i
        fin_cases i
        · exact measurable_snd
        · exact hy
      exact hv.prodMk (Int.measurable_floor.comp (hx.div_const _))
    calc _ ≤ ENNReal.ofReal (N ^ (-f + f / 2)) *
          ((volume : Measure (Fin 2 → ℝ)).prod Measure.count) (zeroRegion K) :=
          measure_density_le_le (Split.mu p k γ) _ (obsMap N 0) hΦ (p.density k γ 0) hgm
            hmap (zeroRegion K) (measurableSet_zeroRegion K)
            (mu_obs_zeroRegion_compl hp k γ) _
      _ ≤ _ := by gcongr; exact zeroRegion_measure_le hK1
  -- total weighted mass splits into the exceptional and the good part
  have hsplit : ∀ γ : Fin (p.1 k), Split.mu p k γ univ ≤
      Split.mu p k γ {z | p.density k γ 0 (obsMap N 0 z) <
          ENNReal.ofReal (N ^ (-f - f / 2)) ∨
        ENNReal.ofReal (N ^ (-f + f / 2)) < p.density k γ 0 (obsMap N 0 z)} +
      Split.mu p k γ
        {z | p.density k γ 0 (obsMap N 0 z) ≤ ENNReal.ofReal (N ^ (-f + f / 2))} := by
    intro γ
    calc Split.mu p k γ univ ≤ Split.mu p k γ
          ({z | p.density k γ 0 (obsMap N 0 z) < ENNReal.ofReal (N ^ (-f - f / 2)) ∨
            ENNReal.ofReal (N ^ (-f + f / 2)) < p.density k γ 0 (obsMap N 0 z)} ∪
           {z | p.density k γ 0 (obsMap N 0 z) ≤ ENNReal.ofReal (N ^ (-f + f / 2))}) := by
          apply measure_mono
          intro z _
          by_cases h : p.density k γ 0 (obsMap N 0 z) ≤ ENNReal.ofReal (N ^ (-f + f / 2))
          · exact Or.inr h
          · exact Or.inl (Or.inr (lt_of_not_ge h))
      _ ≤ _ := measure_union_le _ _
  have hweights := (hp.2.1 k).2.2.1
  have hwnn := (hp.2.1 k).2.1
  have hmass := (hp.2.1 k).2.2.2.2
  -- combine
  have htot : ENNReal.ofReal K⁻¹ ≤ ENNReal.ofReal (N ^ (-c)) +
      ENNReal.ofReal (N ^ (-f + f / 2)) * ENNReal.ofReal (200 * K ^ 3) := by
    calc ENNReal.ofReal K⁻¹
        ≤ ∑ γ, ENNReal.ofReal (p.weight k γ) * Split.mu p k γ univ := hmass
      _ ≤ ∑ γ, ENNReal.ofReal (p.weight k γ) *
          (Split.mu p k γ {z | p.density k γ 0 (obsMap N 0 z) <
              ENNReal.ofReal (N ^ (-f - f / 2)) ∨
            ENNReal.ofReal (N ^ (-f + f / 2)) < p.density k γ 0 (obsMap N 0 z)} +
          ENNReal.ofReal (N ^ (-f + f / 2)) * ENNReal.ofReal (200 * K ^ 3)) := by
          gcongr with γ
          exact (hsplit γ).trans (add_le_add le_rfl (hgood γ))
      _ = (∑ γ, ENNReal.ofReal (p.weight k γ) *
          Split.mu p k γ {z | p.density k γ 0 (obsMap N 0 z) <
              ENNReal.ofReal (N ^ (-f - f / 2)) ∨
            ENNReal.ofReal (N ^ (-f + f / 2)) < p.density k γ 0 (obsMap N 0 z)}) +
          (∑ γ, ENNReal.ofReal (p.weight k γ)) *
            (ENNReal.ofReal (N ^ (-f + f / 2)) * ENNReal.ofReal (200 * K ^ 3)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          congr 1; ext γ; ring
      _ ≤ ENNReal.ofReal (N ^ (-c)) +
          1 * (ENNReal.ofReal (N ^ (-f + f / 2)) * ENNReal.ofReal (200 * K ^ 3)) := by
          gcongr
          · exact hk1
          · have hweights' : ∑ γ, p.weight k γ = 1 := hweights
            rw [← ENNReal.ofReal_sum_of_nonneg (f := fun γ => p.weight k γ)
              (fun γ _ => hwnn γ), hweights', ENNReal.ofReal_one]
      _ = _ := by rw [one_mul]
  -- real form
  have hreal : K⁻¹ ≤ N ^ (-c) + N ^ (-f + f / 2) * (200 * K ^ 3) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)] at htot
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
  -- powers
  have hKc : K ^ 3 ≤ N ^ (3 * c' / 8) := by
    calc K ^ 3 ≤ (N ^ (c' / 8)) ^ 3 := by gcongr
      _ = N ^ (3 * c' / 8) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; ring_nf
  have hKinv : N ^ (-(c' / 8)) ≤ K⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ hKpos hk2
  have hc1 : N ^ (-c) ≤ N ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hc2 : N ^ (-f + f / 2) * (200 * K ^ 3) ≤ 200 * N ^ (-c') := by
    calc N ^ (-f + f / 2) * (200 * K ^ 3) ≤ N ^ (-f + f / 2) * (200 * N ^ (3 * c' / 8)) := by
          gcongr
      _ = 200 * (N ^ (-f + f / 2) * N ^ (3 * c' / 8)) := by ring
      _ = 200 * N ^ (-f + f / 2 + 3 * c' / 8) := by
          rw [Real.rpow_add hNpos (-f + f / 2) (3 * c' / 8)]
      _ ≤ 200 * N ^ (-c') := by
          have : N ^ (-f + f / 2 + 3 * c' / 8) ≤ N ^ (-c') :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
          linarith
  have hfinal : N ^ (-(c' / 8)) ≤ 201 * N ^ (-c') := by linarith
  have hcontra : N ^ (7 * c' / 8) ≤ 201 := by
    have hpos : 0 < N ^ (-c') := Real.rpow_pos_of_pos hNpos _
    have : N ^ (-(c' / 8)) = N ^ (7 * c' / 8) * N ^ (-c') := by
      rw [← Real.rpow_add hNpos]; ring_nf
    rw [this] at hfinal
    nlinarith
  linarith

end

end Submission.Obl.k4_scalar_guarded_entropic_path
