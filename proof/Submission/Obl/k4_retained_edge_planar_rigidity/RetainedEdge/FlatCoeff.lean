-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/FlatCoeff.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.FlatMajorant
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.FlatBridge

/-!
# Flat generated coefficients (paper Lemma 7.4, `re:flat-coefficients`)

Let `ν` be a finite ratio law with values `t`, `|t| ≤ R`, satisfying the interval bound
`ν{t/R ∈ [x - u, x + u]} ≤ K u^S` for `h ≤ u ≤ 1`. For `e₀ > 0` the decay input T4 fixes `n`, and we
fix `k` with `k τ e₀ ≥ 1`. The generated coefficient `C = ∑_{l<k} ∏_{j<n} T_{lj}/R`, with independent
`T_{lj} ∼ ν`, satisfies `P(C ∈ [x - h, x + h]) ≤ 60 h^{1-e₀}` once `h` is small and `K ≤ h^{-e₀ε₀}`.
The characteristic function of `C` is the `k`-th power of that of a product of `n` samples; T4
bounds the latter at all frequencies between `h^{-e₀}` and `h⁻¹`, and the trigonometric majorant
turns this into the window bound.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

set_option linter.unusedSectionVars false

open Complex

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of a tuple `T : Fin k → Fin n → ι` of independent ratio samples. -/
def genW (ν : ι → ℝ) (n k : ℕ) (T : Fin k → Fin n → ι) : ℝ := ∏ l, ∏ j, ν (T l j)

/-- The generated coefficient `∑_{l<k} ∏_{j<n} t(T_{lj})/R`. -/
def genVal (t : ι → ℝ) (R : ℝ) (n k : ℕ) (T : Fin k → Fin n → ι) : ℝ := ∑ l, ∏ j, t (T l j) / R

theorem genW_nonneg {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (n k : ℕ) (T : Fin k → Fin n → ι) :
    0 ≤ genW ν n k T :=
  Finset.prod_nonneg fun l _ => Finset.prod_nonneg fun j _ => hν _

theorem sum_prod_eq_one {ν : ι → ℝ} (hν1 : ∑ i, ν i = 1) (n : ℕ) :
    ∑ U : Fin n → ι, ∏ j, ν (U j) = 1 := by
  rw [← Fintype.prod_sum (ι := Fin n) (κ := fun _ => ι) (fun _ i => ν i)]
  simp [hν1]

theorem sum_genW {ν : ι → ℝ} (hν1 : ∑ i, ν i = 1) (n k : ℕ) : ∑ T, genW ν n k T = 1 := by
  unfold genW
  rw [← Fintype.prod_sum (ι := Fin k) (κ := fun _ => Fin n → ι) (fun _ U => ∏ j, ν (U j))]
  simp [sum_prod_eq_one hν1]

/-- The exponential sum of one product of `n` samples. -/
def prodChf (ν t : ι → ℝ) (R : ℝ) (n : ℕ) (ζ : ℝ) : ℂ :=
  ∑ U : Fin n → ι, ((∏ j, ν (U j) : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * ζ * ∏ j, t (U j) / R : ℝ) : ℂ) * I)

theorem chf_genVal (ν t : ι → ℝ) (R : ℝ) (n k : ℕ) (ζ : ℝ) :
    chf (genW ν n k) (genVal t R n k) ζ = prodChf ν t R n ζ ^ k := by
  rw [← Fin.prod_const k (prodChf ν t R n ζ)]
  unfold chf prodChf genW genVal
  rw [Fintype.prod_sum (ι := Fin k) (κ := fun _ => Fin n → ι)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

theorem norm_prodChf_le {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) (t : ι → ℝ)
    (R : ℝ) (n : ℕ) (ζ : ℝ) : ‖prodChf ν t R n ζ‖ ≤ 1 := by
  unfold prodChf
  calc ‖∑ U : Fin n → ι, ((∏ j, ν (U j) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * ζ * ∏ j, t (U j) / R : ℝ) : ℂ) * I)‖
      ≤ ∑ U : Fin n → ι, ‖((∏ j, ν (U j) : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * ζ * ∏ j, t (U j) / R : ℝ) : ℂ) * I)‖ := norm_sum_le _ _
    _ = ∑ U : Fin n → ι, ∏ j, ν (U j) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hν _)]
    _ = 1 := by
        rw [← Fintype.prod_sum (fun _ i => ν i)]
        simp [hν1]

/-- Integers of a window of radius `X` around `j`. -/
theorem card_near_le (N j : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    (((Finset.range (N + 1)).filter (fun j' : ℕ => |(j : ℝ) - j'| < X)).card : ℝ) ≤ 2 * X + 1 := by
  classical
  have hsub : ((Finset.range (N + 1)).filter (fun j' : ℕ => |(j : ℝ) - j'| < X)).map
      Nat.castEmbedding ⊆ Finset.Icc ⌈(j : ℝ) - X⌉ ⌊(j : ℝ) + X⌋ := by
    intro z hz
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hz
    rw [Finset.mem_filter] at hj'
    have h1 := hj'.2
    rw [abs_lt] at h1
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le]; simp only [Nat.castEmbedding_apply]; push_cast; linarith
    · rw [Int.le_floor]; simp only [Nat.castEmbedding_apply]; push_cast; linarith
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map, Int.card_Icc] at hc
  have hcR : (((Finset.range (N + 1)).filter (fun j' : ℕ => |(j : ℝ) - j'| < X)).card : ℝ) ≤
      ((⌊(j : ℝ) + X⌋ + 1 - ⌈(j : ℝ) - X⌉).toNat : ℝ) := by exact_mod_cast hc
  refine hcR.trans ?_
  have f1 := Int.floor_le ((j : ℝ) + X)
  have f2 := Int.le_ceil ((j : ℝ) - X)
  by_cases hnn : 0 ≤ ⌊(j : ℝ) + X⌋ + 1 - ⌈(j : ℝ) - X⌉
  · have : ((⌊(j : ℝ) + X⌋ + 1 - ⌈(j : ℝ) - X⌉).toNat : ℝ) =
        ((⌊(j : ℝ) + X⌋ + 1 - ⌈(j : ℝ) - X⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    rw [this]; push_cast; linarith
  · push Not at hnn
    rw [Int.toNat_of_nonpos hnn.le]
    push_cast; linarith


/-- The frequency bound: away from `h^{-e₀}` the generated characteristic function is at most `h`. -/
theorem chf_freq_bound {ν t : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) {R : ℝ} (n k : ℕ)
    {τ h e₀ ζ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hk : 1 ≤ e₀ * τ * k) (he₀ : 0 < e₀) (hτ : 0 < τ)
    (hζ : h ^ (-e₀) ≤ |ζ|) (hdecay : ‖prodChf ν t R n ζ‖ ≤ |ζ| ^ (-τ)) :
    ‖chf (genW ν n k) (genVal t R n k) ζ‖ ≤ h := by
  rw [chf_genVal, norm_pow]
  have hpos : 0 < h ^ (-e₀) := Real.rpow_pos_of_pos hh _
  have hζpos : 0 < |ζ| := lt_of_lt_of_le hpos hζ
  have h1 : |ζ| ^ (-τ) ≤ (h ^ (-e₀)) ^ (-τ) :=
    Real.rpow_le_rpow_of_nonpos hpos hζ (by linarith)
  have h2 : (h ^ (-e₀)) ^ (-τ) = h ^ (e₀ * τ) := by
    rw [← Real.rpow_mul hh.le]; ring_nf
  have hb : ‖prodChf ν t R n ζ‖ ≤ h ^ (e₀ * τ) := by rw [← h2]; exact hdecay.trans h1
  calc ‖prodChf ν t R n ζ‖ ^ k ≤ (h ^ (e₀ * τ)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hb k
    _ = h ^ (e₀ * τ * k) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    _ ≤ h ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hh hh1 hk
    _ = h := Real.rpow_one h

/-- **Flat generated coefficients** (paper Lemma 7.4). -/
theorem flat_generated (hT4 : OSSDecay) {S : ℝ} (hS : 0 < S) {e₀ : ℝ} (he₀ : 0 < e₀)
    (he₀1 : e₀ ≤ 1) :
    ∃ n k : ℕ, ∃ η₀ h₁ : ℝ, 0 < η₀ ∧ 0 < h₁ ∧ ∀ h : ℝ, 0 < h → h < h₁ →
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ν t : κ → ℝ) (R K : ℝ), 0 < R →
        (∀ i, 0 ≤ ν i) → ∑ i, ν i = 1 → (∀ i, |t i| ≤ R) → K ≤ h ^ (-η₀) →
        (∀ x u : ℝ, h ≤ u → u ≤ 1 →
          (∑ i, if t i / R ∈ Set.Icc (x - u) (x + u) then ν i else 0) ≤ K * u ^ S) →
        ∀ x : ℝ, lawMass (genW ν n k) (genVal t R n k) (Set.Icc (x - h) (x + h)) ≤
          60 * h ^ (1 - e₀) := by
  set s := min S 1 with hsdef
  have hs : 0 < s := lt_min hS one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsS : s ≤ S := min_le_left _ _
  obtain ⟨n, -, r₀, ε₀, τ, hr₀, hε₀, hτ, hdec⟩ := ossDecay_discrete hT4 hs hs1
  set k := ⌈1 / (e₀ * τ)⌉₊ with hkdef
  have hk : 1 ≤ e₀ * τ * k := by
    have := Nat.le_ceil (1 / (e₀ * τ))
    rw [← hkdef] at this
    have hpos : 0 < e₀ * τ := by positivity
    rw [div_le_iff₀ hpos] at this
    linarith
  refine ⟨n, k, e₀ * ε₀, min 1 (r₀ ^ (1 / e₀)) / 2, by positivity,
    by have := Real.rpow_pos_of_pos hr₀ (1 / e₀); positivity, ?_⟩
  intro h hh hh₁ κ _ _ ν t R K hR hν hν1 ht hK hfrost x
  have hh1 : h < 1 := by
    have : min 1 (r₀ ^ (1 / e₀)) / 2 < 1 := by
      have := min_le_left 1 (r₀ ^ (1 / e₀)); linarith
    linarith
  have hhe : h ^ e₀ < r₀ := by
    have h2 : h < r₀ ^ (1 / e₀) := by
      have := min_le_right 1 (r₀ ^ (1 / e₀))
      have : 0 < r₀ ^ (1 / e₀) := Real.rpow_pos_of_pos hr₀ _
      linarith
    calc h ^ e₀ < (r₀ ^ (1 / e₀)) ^ e₀ := Real.rpow_lt_rpow hh.le h2 he₀
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, one_div, inv_mul_cancel₀ he₀.ne', Real.rpow_one]
  set N := ⌈1 / h⌉₊ with hNdef
  have hN1 : (1 : ℝ) / h ≤ N := Nat.le_ceil _
  have hN : 1 ≤ N := by
    have : (1 : ℝ) < 1 / h := by rw [lt_div_iff₀ hh]; linarith
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set H := 2 * Real.pi * N * h with hH
  have hHpos : 0 < H := by positivity
  set X := H * h ^ (-e₀) with hX
  have hX0 : 0 ≤ X := by positivity
  -- each characteristic-function value is at most 1, or at most `h` at high frequency
  have hterm : ∀ j ∈ Finset.range (N + 1), ∀ j' ∈ Finset.range (N + 1),
      ‖chf (genW ν n k) (genVal t R n k) (((j : ℝ) - j') / H)‖ ≤
        if |(j : ℝ) - j'| < X then 1 else h := by
    intro j hj j' hj'
    split_ifs with hnear
    · rw [chf_genVal, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_prodChf_le hν hν1 t R n _)
    · push Not at hnear
      set ζ := ((j : ℝ) - j') / H with hζdef
      have hζabs : |ζ| = |(j : ℝ) - j'| / H := by rw [hζdef, abs_div, abs_of_pos hHpos]
      have hζlow : h ^ (-e₀) ≤ |ζ| := by
        rw [hζabs, le_div_iff₀ hHpos]; linarith
      have hjN : |(j : ℝ) - j'| ≤ N := by
        have h1 : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h2 : (j' : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj')
        rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j),
          (Nat.cast_nonneg j' : (0 : ℝ) ≤ j')]
      have hζup : |ζ| ≤ 1 / h := by
        rw [hζabs, div_le_div_iff₀ hHpos hh]
        have : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        calc |(j : ℝ) - j'| * h ≤ N * h := by gcongr
          _ ≤ 1 * H := by rw [hH]; nlinarith
      have hpos : 0 < h ^ (-e₀) := Real.rpow_pos_of_pos hh _
      have hζpos : 0 < |ζ| := lt_of_lt_of_le hpos hζlow
      set r := |ζ|⁻¹ with hr
      have hrpos : 0 < r := inv_pos.mpr hζpos
      have hr_le : r ≤ h ^ e₀ := by
        rw [hr, inv_le_comm₀ hζpos (Real.rpow_pos_of_pos hh _), ← Real.rpow_neg hh.le]
        exact hζlow
      have hr_ge : h ≤ r := by
        rw [hr, le_inv_comm₀ hh hζpos]
        rwa [one_div] at hζup
      have hrr₀ : r < r₀ := lt_of_le_of_lt hr_le hhe
      have hy : ∀ i, t i / R ∈ Set.Icc (-1 : ℝ) 1 := by
        intro i
        have := ht i
        rw [Set.mem_Icc, le_div_iff₀ hR, div_le_iff₀ hR]
        rw [abs_le] at this
        constructor <;> linarith
      have hKr : K ≤ r ^ (-ε₀) := by
        calc K ≤ h ^ (-(e₀ * ε₀)) := hK
          _ = (h ^ e₀) ^ (-ε₀) := by rw [← Real.rpow_mul hh.le]; ring_nf
          _ ≤ r ^ (-ε₀) := Real.rpow_le_rpow_of_nonpos hrpos hr_le (by linarith)
      have hfrost' : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
          (∑ i, if (fun i => t i / R) i ∈ Set.Icc (x - u) (x + u) then ν i else 0) ≤
            r ^ (-ε₀) * u ^ s := by
        intro x u hu hu1
        have hupos : 0 < u := lt_of_lt_of_le hrpos hu
        calc (∑ i, if (fun i => t i / R) i ∈ Set.Icc (x - u) (x + u) then ν i else 0)
            ≤ K * u ^ S := hfrost x u (le_trans hr_ge hu) hu1
          _ ≤ r ^ (-ε₀) * u ^ s := by
              have hus : u ^ S ≤ u ^ s := Real.rpow_le_rpow_of_exponent_ge hupos hu1 hsS
              have hK0 : 0 ≤ K := by
                have := hfrost x 1 (le_of_lt hh1) le_rfl
                have h0 : 0 ≤ ∑ i, if t i / R ∈ Set.Icc (x - 1) (x + 1) then ν i else (0 : ℝ) :=
                  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hν i]
                rw [Real.one_rpow, mul_one] at this
                linarith
              gcongr
      have hdecay := hdec r hrpos hrr₀ κ ν (fun i => t i / R) hν hν1 hy hfrost' ζ
        (by rw [hr, inv_inv]) (by rw [hr, inv_inv]; linarith)
      have hdecay' : ‖prodChf ν t R n ζ‖ ≤ |ζ| ^ (-τ) := by
        unfold prodChf
        convert hdecay using 3
      exact chf_freq_bound hν hν1 n k hh hh1.le hk he₀ hτ hζlow hdecay'
  -- sum the bounds
  have hsum : ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
      ‖chf (genW ν n k) (genVal t R n k) (((j : ℝ) - j') / H)‖ ≤
        ((N : ℝ) + 1) * (2 * X + 1 + ((N : ℝ) + 1) * h) := by
    calc ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
          ‖chf (genW ν n k) (genVal t R n k) (((j : ℝ) - j') / H)‖
        ≤ ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
            ((if |(j : ℝ) - j'| < X then (1 : ℝ) else 0) + h) := by
          refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun j' hj' => ?_
          refine (hterm j hj j' hj').trans ?_
          split_ifs <;> linarith
      _ ≤ ∑ _j ∈ Finset.range (N + 1), (2 * X + 1 + ((N : ℝ) + 1) * h) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_filter]
          have hc := card_near_le N j hX0
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          push_cast
          linarith
      _ = ((N : ℝ) + 1) * (2 * X + 1 + ((N : ℝ) + 1) * h) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hmaj := lawMass_window_le_chf (genW_nonneg hν n k) (genVal t R n k) hh N hN x
  have hN1' : (1 : ℝ) / ((N : ℝ) + 1) ≤ h := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hh] at hN1
    nlinarith
  have hX' : X = 2 * Real.pi * N * h ^ (1 - e₀) := by
    rw [hX, hH, sub_eq_add_neg, Real.rpow_add hh, Real.rpow_one]; ring
  have hhe1 : h ≤ h ^ (1 - e₀) := by
    calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
      _ ≤ h ^ (1 - e₀) := Real.rpow_le_rpow_of_exponent_ge hh hh1.le (by linarith)
  have hpi := Real.pi_lt_d2
  have hhe0 : 0 ≤ h ^ (1 - e₀) := (Real.rpow_pos_of_pos hh _).le
  calc lawMass (genW ν n k) (genVal t R n k) (Set.Icc (x - h) (x + h))
      ≤ 4 / ((N : ℝ) + 1) ^ 2 * ∑ j ∈ Finset.range (N + 1), ∑ j' ∈ Finset.range (N + 1),
          ‖chf (genW ν n k) (genVal t R n k) (((j : ℝ) - j') / (2 * Real.pi * N * h))‖ := hmaj
    _ ≤ 4 / ((N : ℝ) + 1) ^ 2 * (((N : ℝ) + 1) * (2 * X + 1 + ((N : ℝ) + 1) * h)) := by
        gcongr
    _ = 8 * X / ((N : ℝ) + 1) + 4 * (1 / ((N : ℝ) + 1)) + 4 * h := by
        field_simp
        ring
    _ ≤ 16 * Real.pi * h ^ (1 - e₀) + 4 * h + 4 * h := by
        have h8 : 8 * X / ((N : ℝ) + 1) ≤ 16 * Real.pi * h ^ (1 - e₀) := by
          rw [hX', div_le_iff₀ (by positivity)]
          have : 0 ≤ Real.pi * h ^ (1 - e₀) := by positivity
          nlinarith
        linarith
    _ ≤ 60 * h ^ (1 - e₀) := by nlinarith

end

end Submission.Obl.k4_retained_edge_planar_rigidity
