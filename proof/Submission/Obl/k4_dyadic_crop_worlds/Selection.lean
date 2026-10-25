import Mathlib

/-!
# Selecting a heavy dyadic mass class along a subsequence

Pure real analysis behind the crop worlds of `k4_dyadic_crop_worlds`. Finitely many boxes carry
prior masses `P` (summing to at most one) and selected masses `0 ≤ S ≤ P`, with total selected
mass at least `K₀⁻¹`. Boxes of prior mass below `N^-(A+1)` carry at most `N^-1` in all. The
remaining boxes fall into `O(log N)` dyadic classes `2^c ≤ P < 2^(c+1)`; a class of largest
selected mass keeps a `1/(2 K₀ (J+1))` share. Along a subsequence the class exponents converge,
which gives the common mass exponent `β`.
-/

open Filter Finset
open scoped Topology

namespace Submission.Obl.k4_dyadic_crop_worlds

noncomputable section

/-- `C log x + C` is eventually below `x ^ ε`. -/
lemma eventually_mul_log_add_le_rpow (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x + C ≤ x ^ ε := by
  have hC : 0 < |C| + 1 := by positivity
  have h1 := (isLittleO_log_rpow_atTop hε).bound
    (show (0 : ℝ) < 1 / (2 * (|C| + 1)) by positivity)
  have h2 : Tendsto (fun x : ℝ => x ^ ε) atTop atTop := tendsto_rpow_atTop hε
  filter_upwards [h1, h2.eventually_ge_atTop (2 * (|C| + 1)), eventually_ge_atTop (1 : ℝ)]
    with x hx hxε hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxpos : 0 ≤ x ^ ε := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hxpos] at hx
  have hCa : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have h3 : C * Real.log x ≤ (|C| + 1) * Real.log x := mul_le_mul_of_nonneg_right hCa hlog
  have h4 : (|C| + 1) * Real.log x ≤ x ^ ε / 2 := by
    calc (|C| + 1) * Real.log x ≤ (|C| + 1) * (1 / (2 * (|C| + 1)) * x ^ ε) :=
          mul_le_mul_of_nonneg_left hx hC.le
      _ = x ^ ε / 2 := by field_simp
  linarith

/-- The number of dyadic classes used at resolution `N`. -/
def classCount (A : ℕ) (N : ℝ) : ℕ := ⌈((A : ℝ) + 1) * Real.logb 2 N⌉₊

lemma two_rpow_neg_mul_logb {N : ℝ} (hN : 0 < N) (x : ℝ) :
    (2 : ℝ) ^ (-x * Real.logb 2 N) = N ^ (-x) := by
  rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) hN]

/-- One resolution: a heavy dyadic class of boxes. -/
lemma exists_heavy_class {ι : Type*} [DecidableEq ι] (F : Finset ι) (P S : ι → ℝ)
    {N : ℝ} (hN : 2 ≤ N) (A : ℕ)
    (hS0 : ∀ q, 0 ≤ S q) (hSP : ∀ q, S q ≤ P q) (hP1 : ∑ q ∈ F, P q ≤ 1) :
    ∃ (c : ℤ) (Q : Finset ι), Q ⊆ F ∧ -((classCount A N : ℕ) : ℤ) ≤ c ∧ c ≤ 0 ∧
      (∀ q ∈ Q, N ^ (-((A : ℝ) + 1)) ≤ P q ∧ (2 : ℝ) ^ c ≤ P q ∧ P q < (2 : ℝ) ^ (c + 1)) ∧
      ∑ q ∈ F, S q - (F.card : ℝ) * N ^ (-((A : ℝ) + 1)) ≤
        ((classCount A N : ℝ) + 1) * ∑ q ∈ Q, S q := by
  classical
  set δ : ℝ := N ^ (-((A : ℝ) + 1)) with hδ
  set J : ℕ := classCount A N with hJ
  have hNpos : 0 < N := by linarith
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hP0 : ∀ q, 0 ≤ P q := fun q => (hS0 q).trans (hSP q)
  set G := F.filter (fun q => δ ≤ P q) with hG
  set cls : ι → ℤ := fun q => Int.log 2 (P q) with hcls
  have hcls_lo : ∀ q, 0 < P q → (2 : ℝ) ^ cls q ≤ P q := by
    intro q hq
    have := Int.zpow_log_le_self (b := 2) (R := ℝ) (by norm_num) hq
    simpa using this
  have hcls_hi : ∀ q, P q < (2 : ℝ) ^ (cls q + 1) := by
    intro q
    have := Int.lt_zpow_succ_log_self (b := 2) (R := ℝ) (by norm_num) (P q)
    simpa using this
  have hmaps : ∀ q ∈ G, cls q ∈ Icc (-(J : ℤ)) 0 := by
    intro q hq
    rw [hG, mem_filter] at hq
    have hPq : 0 < P q := hδpos.trans_le hq.2
    have hP1q : P q ≤ 1 := (single_le_sum (fun i _ => hP0 i) hq.1).trans hP1
    rw [mem_Icc]
    constructor
    · by_contra hlt
      push Not at hlt
      have h1 : cls q + 1 ≤ -(J : ℤ) := by omega
      have h2 : (2 : ℝ) ^ (cls q + 1) ≤ (2 : ℝ) ^ (-(J : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) h1
      have h3 : (2 : ℝ) ^ (-(J : ℤ)) ≤ δ := by
        rw [hδ, ← two_rpow_neg_mul_logb hNpos, ← Real.rpow_intCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : ((A : ℝ) + 1) * Real.logb 2 N ≤ (J : ℝ) := Nat.le_ceil _
        push_cast
        linarith
      linarith [hcls_hi q]
    · have h1 : (2 : ℝ) ^ cls q ≤ 1 := (hcls_lo q hPq).trans hP1q
      exact (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1
  set T : ℤ → ℝ := fun j => ∑ q ∈ G with cls q = j, S q with hT
  have hsumT : ∑ j ∈ Icc (-(J : ℤ)) 0, T j = ∑ q ∈ G, S q :=
    sum_fiberwise_of_maps_to hmaps S
  obtain ⟨c, hc, hcmax⟩ := (Icc (-(J : ℤ)) 0).exists_max_image T ⟨0, by simp⟩
  have hcard : ((Icc (-(J : ℤ)) 0).card : ℝ) = (J : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (0 + 1 - -(J : ℤ)).toNat = J + 1 := by omega
    rw [this]
    push_cast
    ring
  have hTle : ∑ j ∈ Icc (-(J : ℤ)) 0, T j ≤ ((J : ℝ) + 1) * T c := by
    have := sum_le_card_nsmul (Icc (-(J : ℤ)) 0) T (T c) hcmax
    rw [nsmul_eq_mul, hcard] at this
    exact this
  have hsplit : ∑ q ∈ F, S q = ∑ q ∈ G, S q + ∑ q ∈ F.filter (fun q => ¬ δ ≤ P q), S q :=
    (sum_filter_add_sum_filter_not F (fun q => δ ≤ P q) S).symm
  have hsmall : ∑ q ∈ F.filter (fun q => ¬ δ ≤ P q), S q ≤ (F.card : ℝ) * δ := by
    calc ∑ q ∈ F.filter (fun q => ¬ δ ≤ P q), S q
        ≤ ∑ q ∈ F.filter (fun q => ¬ δ ≤ P q), δ := by
          apply sum_le_sum
          intro q hq
          rw [mem_filter] at hq
          push Not at hq
          exact (hSP q).trans hq.2.le
      _ = ((F.filter (fun q => ¬ δ ≤ P q)).card : ℝ) * δ := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (F.card : ℝ) * δ := by
          apply mul_le_mul_of_nonneg_right _ hδpos.le
          exact_mod_cast card_filter_le _ _
  refine ⟨c, G.filter (fun q => cls q = c), ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [mem_filter, hG, mem_filter] at hq
    exact hq.1.1
  · exact (mem_Icc.1 hc).1
  · exact (mem_Icc.1 hc).2
  · intro q hq
    rw [mem_filter, hG, mem_filter] at hq
    have hPq : 0 < P q := hδpos.trans_le hq.1.2
    refine ⟨hq.1.2, ?_, ?_⟩
    · rw [← hq.2]; exact hcls_lo q hPq
    · rw [← hq.2]; exact hcls_hi q
  · have : ∑ q ∈ G.filter (fun q => cls q = c), S q = T c := rfl
    rw [this]
    linarith

lemma rpow_neg_classExponent {N : ℝ} (hN : 1 < N) (c : ℤ) :
    N ^ (-(-(c : ℝ) * Real.log 2 / Real.log N)) = (2 : ℝ) ^ c := by
  have hNpos : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  rw [Real.rpow_def_of_pos hNpos, ← Real.rpow_intCast,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp

/-- Selection of a heavy dyadic mass class with a common mass exponent along a subsequence. -/
theorem exists_common_mass_class
    (N K₀ : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK1 : ∀ k, 1 ≤ K₀ k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K₀ k ≤ N k ^ ε)
    {ι : Type*} [DecidableEq ι] (F : ℕ → Finset ι) (P S : ℕ → ι → ℝ) (A : ℕ)
    (hF : ∀ k, ((F k).card : ℝ) ≤ N k ^ A)
    (hS0 : ∀ k q, 0 ≤ S k q) (hSP : ∀ k q, S k q ≤ P k q)
    (hP1 : ∀ k, ∑ q ∈ F k, P k q ≤ 1)
    (hmass : ∀ k, (K₀ k)⁻¹ ≤ ∑ q ∈ F k, S k q) :
    ∃ (ψ : ℕ → ℕ) (Q : ℕ → Finset ι) (β : ℝ) (K : ℕ → ℝ),
      StrictMono ψ ∧ (∀ k, Q k ⊆ F (ψ k)) ∧
      (∀ k, ∀ q ∈ Q k, N (ψ k) ^ (-((A : ℝ) + 1)) ≤ P (ψ k) q) ∧
      (∀ k, 1 ≤ K k) ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N (ψ k) ^ ε) ∧
      (∀ k, (K k)⁻¹ ≤ ∑ q ∈ Q k, S (ψ k) q) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ q ∈ Q k,
        N (ψ k) ^ (-β - ε) ≤ P (ψ k) q ∧ P (ψ k) q ≤ N (ψ k) ^ (-β + ε)) := by
  classical
  choose c Q hQF hclo hchi hQP hQS using
    fun k => exists_heavy_class (F k) (P k) (S k) (hN k) A (hS0 k) (hSP k) (hP1 k)
  have hN1 : ∀ k, 1 < N k := fun k => by linarith [hN k]
  have hNpos : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hlogN : ∀ k, Real.log 2 ≤ Real.log (N k) := fun k =>
    Real.log_le_log (by norm_num) (hN k)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set β' : ℕ → ℝ := fun k => -(c k : ℝ) * Real.log 2 / Real.log (N k) with hβ'
  -- the class exponents are bounded
  have hβ'mem : ∀ k, β' k ∈ Set.Icc (0 : ℝ) ((A : ℝ) + 2) := by
    intro k
    have hlogpos : 0 < Real.log (N k) := Real.log_pos (hN1 k)
    have hc0 : (c k : ℝ) ≤ 0 := by exact_mod_cast hchi k
    have hcJ : -((classCount A (N k) : ℕ) : ℝ) ≤ (c k : ℝ) := by exact_mod_cast hclo k
    have hJle : (classCount A (N k) : ℝ) ≤ ((A : ℝ) + 1) * Real.logb 2 (N k) + 1 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ ((A : ℝ) + 1) * Real.logb 2 (N k) by
        apply mul_nonneg (by positivity)
        exact Real.logb_nonneg (by norm_num) (by linarith [hN k]))
      exact this.le
    constructor
    · apply div_nonneg _ hlogpos.le
      nlinarith
    · rw [div_le_iff₀ hlogpos]
      have hlb : Real.logb 2 (N k) * Real.log 2 = Real.log (N k) := by
        rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
      have : -(c k : ℝ) * Real.log 2 ≤
          (((A : ℝ) + 1) * Real.logb 2 (N k) + 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2.le
      nlinarith [hlogN k]
  obtain ⟨β, -, φ, hφ, hβlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) ((A : ℝ) + 2)) hβ'mem
  -- a tail where the light boxes cost at most half the selected mass
  have hhalf : ∀ᶠ k in atTop, 2 * K₀ k ≤ N k := by
    filter_upwards [hKsub (1 / 2) (by norm_num), hNt.eventually_ge_atTop 4] with k hk hk4
    have hsq : N k ^ (1 / 2 : ℝ) * N k ^ (1 / 2 : ℝ) = N k := by
      rw [← Real.rpow_add (hNpos k)]; norm_num
    have h2 : 2 ≤ N k ^ (1 / 2 : ℝ) := by
      have : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := this.symm
        _ ≤ N k ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hk4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith [Real.rpow_nonneg (hNpos k).le (1 / 2 : ℝ)]
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hhalf
  set ψ : ℕ → ℕ := fun k => φ (k + k₀) with hψdef
  have hψ : StrictMono ψ := fun a b hab => hφ (by omega)
  have hψk₀ : ∀ k, k₀ ≤ ψ k := fun k => by
    exact le_trans (Nat.le_add_left k₀ k) (hφ.id_le (k + k₀))
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  set K : ℕ → ℝ := fun k => 2 * K₀ (ψ k) * ((classCount A (N (ψ k)) : ℝ) + 1) with hKdef
  refine ⟨ψ, fun k => Q (ψ k), β, K, hψ, fun k => hQF (ψ k), ?_, ?_, ?_, ?_, ?_⟩
  · intro k q hq
    exact (hQP (ψ k) q hq).1
  · intro k
    have := hK1 (ψ k)
    have : (0 : ℝ) ≤ classCount A (N (ψ k)) := Nat.cast_nonneg _
    simp only [hKdef]
    nlinarith
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hlogC := eventually_mul_log_add_le_rpow (2 * ((A : ℝ) + 1) / Real.log 2 + 4) hε2
    have h1 : ∀ᶠ n in atTop, 2 * ((classCount A (N n) : ℝ) + 1) ≤ N n ^ (ε / 2) := by
      filter_upwards [hNt.eventually hlogC] with n hn
      have hJle : (classCount A (N n) : ℝ) ≤ ((A : ℝ) + 1) * Real.logb 2 (N n) + 1 := by
        have := Nat.ceil_lt_add_one (show 0 ≤ ((A : ℝ) + 1) * Real.logb 2 (N n) by
          apply mul_nonneg (by positivity)
          exact Real.logb_nonneg (by norm_num) (by linarith [hN n]))
        exact this.le
      have hlogpos : 0 ≤ Real.log (N n) := Real.log_nonneg (by linarith [hN n])
      have hlb : ((A : ℝ) + 1) * Real.logb 2 (N n) =
          ((A : ℝ) + 1) / Real.log 2 * Real.log (N n) := by
        rw [Real.logb]; ring
      have hAl : 0 ≤ ((A : ℝ) + 1) / Real.log 2 * Real.log (N n) := by positivity
      have e1 : (2 * ((A : ℝ) + 1) / Real.log 2 + 4) * Real.log (N n) =
          2 * (((A : ℝ) + 1) / Real.log 2 * Real.log (N n)) + 4 * Real.log (N n) := by ring
      have e2 : 0 ≤ 2 * ((A : ℝ) + 1) / Real.log 2 := by positivity
      linarith
    have h2 := hKsub (ε / 2) hε2
    filter_upwards [hψt.eventually h1, hψt.eventually h2] with k hk1 hk2
    have hNk := hNpos (ψ k)
    have : N (ψ k) ^ (ε / 2) * N (ψ k) ^ (ε / 2) = N (ψ k) ^ ε := by
      rw [← Real.rpow_add hNk]; ring_nf
    have hJ0 : (0 : ℝ) ≤ classCount A (N (ψ k)) := Nat.cast_nonneg _
    have hK0 := hK1 (ψ k)
    simp only [hKdef]
    calc 2 * K₀ (ψ k) * ((classCount A (N (ψ k)) : ℝ) + 1)
        = K₀ (ψ k) * (2 * ((classCount A (N (ψ k)) : ℝ) + 1)) := by ring
      _ ≤ N (ψ k) ^ (ε / 2) * N (ψ k) ^ (ε / 2) :=
          mul_le_mul hk2 hk1 (by positivity) (Real.rpow_nonneg hNk.le _)
      _ = N (ψ k) ^ ε := this
  · intro k
    have hk := hk₀ (ψ k) (hψk₀ k)
    have hNk := hNpos (ψ k)
    have hK0 := hK1 (ψ k)
    have hJ0 : (0 : ℝ) ≤ classCount A (N (ψ k)) := Nat.cast_nonneg _
    have hδ : ((F (ψ k)).card : ℝ) * N (ψ k) ^ (-((A : ℝ) + 1)) ≤ (N (ψ k))⁻¹ := by
      calc ((F (ψ k)).card : ℝ) * N (ψ k) ^ (-((A : ℝ) + 1))
          ≤ N (ψ k) ^ A * N (ψ k) ^ (-((A : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hF (ψ k)) (Real.rpow_nonneg hNk.le _)
        _ = (N (ψ k))⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hNk]
            rw [show (A : ℝ) + -((A : ℝ) + 1) = -1 by ring, Real.rpow_neg_one]
    have hinv : (N (ψ k))⁻¹ ≤ (2 * K₀ (ψ k))⁻¹ :=
      inv_anti₀ (by positivity) hk
    have hm := hmass (ψ k)
    have hS := hQS (ψ k)
    have hpos : 0 < (classCount A (N (ψ k)) : ℝ) + 1 := by positivity
    simp only [hKdef]
    rw [mul_inv, mul_inv]
    have : (2 * K₀ (ψ k))⁻¹ = (2 : ℝ)⁻¹ * (K₀ (ψ k))⁻¹ := mul_inv 2 _
    rw [← this]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have h2K : (2 * K₀ (ψ k))⁻¹ = (K₀ (ψ k))⁻¹ - (2 * K₀ (ψ k))⁻¹ := by
      field_simp; ring
    linarith
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hlim : Tendsto (fun k => β' (ψ k)) atTop (𝓝 β) :=
      hβlim.comp (tendsto_add_atTop_nat k₀)
    have hclose : ∀ᶠ k in atTop, |β' (ψ k) - β| < ε / 2 := by
      have := (Metric.tendsto_nhds.1 hlim) (ε / 2) hε2
      filter_upwards [this] with k hk
      rwa [Real.dist_eq] at hk
    have hbig : ∀ᶠ k in atTop, (2 : ℝ) ≤ N (ψ k) ^ (ε / 2) := by
      have h := (tendsto_rpow_atTop hε2).comp hNt
      exact hψt.eventually (h.eventually_ge_atTop 2)
    filter_upwards [hclose, hbig] with k hk hk2 q hq
    have hNk := hNpos (ψ k)
    have hN1k := hN1 (ψ k)
    obtain ⟨-, hlo, hhi⟩ := hQP (ψ k) q hq
    have h2c : N (ψ k) ^ (-β' (ψ k)) = (2 : ℝ) ^ c (ψ k) := rpow_neg_classExponent hN1k _
    rw [abs_lt] at hk
    constructor
    · calc N (ψ k) ^ (-β - ε) ≤ N (ψ k) ^ (-β' (ψ k)) :=
            Real.rpow_le_rpow_of_exponent_le hN1k.le (by linarith)
        _ = (2 : ℝ) ^ c (ψ k) := h2c
        _ ≤ P (ψ k) q := hlo
    · have h2c1 : (2 : ℝ) ^ (c (ψ k) + 1) = 2 * N (ψ k) ^ (-β' (ψ k)) := by
        rw [zpow_add₀ (by norm_num), zpow_one, h2c]; ring
      calc P (ψ k) q ≤ (2 : ℝ) ^ (c (ψ k) + 1) := hhi.le
        _ = 2 * N (ψ k) ^ (-β' (ψ k)) := h2c1
        _ ≤ N (ψ k) ^ (ε / 2) * N (ψ k) ^ (-β' (ψ k)) :=
            mul_le_mul_of_nonneg_right hk2 (Real.rpow_nonneg hNk.le _)
        _ = N (ψ k) ^ (ε / 2 + -β' (ψ k)) := (Real.rpow_add hNk _ _).symm
        _ ≤ N (ψ k) ^ (-β + ε) :=
            Real.rpow_le_rpow_of_exponent_le hN1k.le (by linarith)

end

end Submission.Obl.k4_dyadic_crop_worlds
