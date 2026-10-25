import Submission.Lib.K4ExactProblemOps.Reindex

/-!
# Rescaling the base of an exact problem

Replacing the base sequence `N` by `N ^ c` (`c > 0`) divides depths, horizons and
logarithmic density exponents by `c`: the thickness satisfies
`δ (N ^ c) r = δ N (c * r)` exactly.  A valid problem of length `L` becomes a valid
problem of length `L / c`, with profile `r ↦ f (c * r) / c`, the same dimension cap
`d` and the same angular parameters `S, η`, and its horizon is divided by `c`
(paper §4.1: "Scaling N to N^L reduces the numerical optimization to length one").
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory Filter
open scoped Pointwise

theorem δ_rpow {N : ℝ} (hN : 0 < N) (c r : ℝ) : δ (N ^ c) r = δ N (c * r) := by
  unfold δ
  rw [Real.log_rpow hN]
  congr 4
  ring

theorem pow_le_rpow_pow {N : ℝ} (hN : 1 ≤ N) {c : ℝ} {M M' : ℕ} (hM : (M : ℝ) ≤ c * M') :
    N ^ M ≤ (N ^ c) ^ M' := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hN hM

theorem rpow_pow_le_pow {N : ℝ} (hN : 1 ≤ N) {c : ℝ} {M M' : ℕ} (hM : c * M' ≤ (M : ℝ)) :
    (N ^ c) ^ M' ≤ N ^ M := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hN hM

/-- The tempered-data block of `prob`, for a given complexity `M, D`. -/
def ProbBlock (N K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ)
    (M D : ℕ) : Prop :=
  ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ

/-- The tempered-data block only uses the scale through the bound `N k ^ M`. -/
theorem ProbBlock.transfer {N N' K : ℕ → ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {M M' D : ℕ} (h : ProbBlock N K W ω ν E P B M D) (hpow : ∀ k, N k ^ M ≤ N' k ^ M') :
    ProbBlock N' K W ω ν E P B M' D := by
  intro k
  obtain ⟨hW, hω, hsum, hγ, hK⟩ := h k
  refine ⟨hW.trans (hpow k), hω, hsum, fun γ => ?_, hK⟩
  obtain ⟨hprob, hB0, hB1, hB2, hdeg, hcoeff, ⟨m, hm, c, i, A, hcA, hν⟩, hEm, hEsub, hEbd,
    hEfmt, hae1, hae2⟩ := hγ γ
  refine ⟨hprob, hB0, hB1.trans (hpow k), hB2.trans (hpow k), hdeg,
    fun b => (hcoeff b).trans (hpow k), ⟨m, hm.trans (hpow k), c, i, A, fun j => ?_, hν⟩,
    hEm, hEsub, fun p hp => ?_, fun i => fmt_mono (hEfmt i) (hpow k), hae1, hae2⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hcA j
    exact ⟨h1, h2.trans (hpow k), h3.trans (hpow k), fmt_mono h4 (hpow k),
      fun x hx b => (h5 x hx b).trans (hpow k)⟩
  · obtain ⟨h1, h2⟩ := hEbd p hp
    exact ⟨h1.trans (hpow k), fun e => (h2 e).trans (hpow k)⟩

section

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- Rescaling the base by `c > 0` gives a valid problem of length `L / c`. -/
theorem prob_rescale (hp : prob N K L d S η W ω ν E P B f g G) {c : ℝ} (hc : 0 < c)
    (hN : ∀ k, 2 ≤ N k ^ c) :
    prob (fun k => N k ^ c) K (L / c) d S η W ω ν E P B (fun r => f (c * r) / c)
      (fun k γ r => g k γ (c * r)) (fun k γ u => G k γ (c * u)) := by
  obtain ⟨hN2, hNtend, ⟨hK1, hKε⟩, hL, hd, hd1, hS, hη, ⟨M, D, hMD⟩, hg, hG, hf, htyp,
    hcap, hang⟩ := hp
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le (by norm_num) (hN2 k)
  have hN1 : ∀ k, 1 ≤ N k := fun k => le_trans (by norm_num) (hN2 k)
  have hrp : ∀ k (e : ℝ), (N k ^ c) ^ e = N k ^ (c * e) := fun k e =>
    (Real.rpow_mul (hNpos k).le c e).symm
  have hcc : c * (L / c) = L := mul_div_cancel₀ L hc.ne'
  have hle : ∀ r : ℝ, r ≤ L / c → c * r ≤ L := fun r hr => by
    rw [le_div_iff₀ hc] at hr
    linarith
  have hM : (M : ℝ) ≤ c * (⌈(M : ℝ) / c⌉₊ : ℕ) := by
    have := Nat.le_ceil ((M : ℝ) / c)
    rw [div_le_iff₀ hc] at this
    linarith
  refine ⟨hN, (tendsto_rpow_atTop hc).comp hNtend, ⟨hK1, fun ε hε => ?_⟩, div_pos hL hc, hd,
    hd1, hS, hη, ⟨⌈(M : ℝ) / c⌉₊, D, ProbBlock.transfer (N := N) hMD
      (fun k => pow_le_rpow_pow (hN1 k) hM)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hKε (c * ε) (by positivity)] with k hk
    rwa [hrp]
  · intro k γ r hr hrL
    rw [δ_rpow (hNpos k)]
    exact hg k γ (c * r) (by positivity) (hle r hrL)
  · intro k γ u hu huL
    have hcu : c * u ≤ η * L := by
      have := mul_le_mul_of_nonneg_left huL hc.le
      calc c * u ≤ c * (η * (L / c)) := this
        _ = η * L := by field_simp
    rw [δ_rpow (hNpos k), δ_rpow (hNpos k), hcc]
    exact hG k γ (c * u) (by positivity) hcu
  · intro r s hr hrs hsL
    obtain ⟨h1, h2⟩ := hf (c * r) (c * s) (by positivity)
      (mul_le_mul_of_nonneg_left hrs hc.le) (hle s hsL)
    refine ⟨?_, ?_⟩
    · rw [← sub_div]
      exact div_nonneg h1 hc.le
    · rw [← sub_div, div_le_iff₀ hc]
      linarith
  · intro r τ hr hrL hτ
    obtain ⟨c₀, hc₀, hev⟩ := htyp (c * r) (c * τ) (by positivity) (hle r hrL) (by positivity)
    refine ⟨c₀ / c, by positivity, ?_⟩
    filter_upwards [hev] with k hk
    have e1 : c * (-(f (c * r) / c) - τ) = -f (c * r) - c * τ := by field_simp
    have e2 : c * (-(f (c * r) / c) + τ) = -f (c * r) + c * τ := by field_simp
    have e3 : c * (-(c₀ / c)) = -c₀ := by field_simp
    simp only [hrp, e1, e2, e3, δ_rpow (hNpos k)]
    exact hk
  · intro r hr hrL
    have h1 := hcap (c * r) (by positivity) (hle r hrL)
    show f (c * (L / c)) / c - f (c * r) / c ≤ d * (L / c - r)
    rw [hcc]
    rw [← sub_div, div_le_iff₀ hc]
    calc f L - f (c * r) ≤ d * (L - c * r) := h1
      _ = d * (L / c - r) * c := by field_simp
  · intro u τ hu huL hτ
    have hcu : c * u ≤ η * L := by
      have := mul_le_mul_of_nonneg_left huL hc.le
      calc c * u ≤ c * (η * (L / c)) := this
        _ = η * L := by field_simp
    obtain ⟨c₀, hc₀, hev⟩ := hang (c * u) (c * τ) (by positivity) hcu (by positivity)
    refine ⟨c₀ / c, by positivity, ?_⟩
    filter_upwards [hev] with k hk
    have e1 : c * (-(f L / c) - S * u + τ) = -f L - S * (c * u) + c * τ := by
      field_simp
    have e3 : c * (-(c₀ / c)) = -c₀ := by field_simp
    simp only [hrp, e3, δ_rpow (hNpos k), hcc]
    simp only [e1]
    exact hk

/-- Terminal systems correspond under rescaling of the base. -/
theorem term_rescale_iff {c : ℝ} (hc : 0 < c) (hN1 : ∀ k, 1 ≤ N k) (h' : ℝ) :
    term (fun k => N k ^ c) K (L / c) W ω ν E B (fun r => f (c * r) / c) h' ↔
      term N K L W ω ν E B f (c * h') := by
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le (by norm_num) (hN1 k)
  have hrp : ∀ k (e : ℝ), (N k ^ c) ^ e = N k ^ (c * e) := fun k e =>
    (Real.rpow_mul (hNpos k).le c e).symm
  have hcc : c * (L / c) = L := mul_div_cancel₀ L hc.ne'
  have hfl : ∀ k, (N k ^ c) ^ (-((fun r => f (c * r) / c) (L / c))) = N k ^ (-f L) := by
    intro k
    rw [hrp]
    congr 1
    simp only [hcc]
    field_simp
  constructor
  · rintro ⟨M', D, hMD⟩
    refine ⟨⌈c * M'⌉₊, D, fun ε hε => ?_⟩
    have hM : c * (M' : ℝ) ≤ (⌈c * (M' : ℝ)⌉₊ : ℕ) := Nat.le_ceil _
    apply (hMD (ε / c) (by positivity)).mono
    intro k hk
    obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, cc, u, Q, R, A, F, htime, hcount, hdisj, hcharts,
      hmass⟩ := hk
    have hpow : (N k ^ c) ^ M' ≤ N k ^ ⌈c * (M' : ℝ)⌉₊ := rpow_pow_le_pow (hN1 k) hM
    refine ⟨κ, hκ, hKκ, ?_, T, C, γ, j, cc, u, Q, R, A, F, ?_, hcount.trans hpow, hdisj,
      fun b => ?_, hmass⟩
    · rw [hrp] at hκN
      rwa [mul_div_cancel₀ ε hc.ne'] at hκN
    · rwa [hrp] at htime
    · refine chart_transfer (hcharts b) hpow ?_ ?_
      · rw [δ_rpow (hNpos k), hcc]
      · intro hfloor
        rwa [hfl k] at hfloor
  · rintro ⟨M, D, hMD⟩
    refine ⟨⌈(M : ℝ) / c⌉₊, D, fun ε hε => ?_⟩
    have hM : (M : ℝ) ≤ c * (⌈(M : ℝ) / c⌉₊ : ℕ) := by
      have := Nat.le_ceil ((M : ℝ) / c)
      rw [div_le_iff₀ hc] at this
      linarith
    apply (hMD (c * ε) (by positivity)).mono
    intro k hk
    obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, cc, u, Q, R, A, F, htime, hcount, hdisj, hcharts,
      hmass⟩ := hk
    have hpow : N k ^ M ≤ (N k ^ c) ^ ⌈(M : ℝ) / c⌉₊ := pow_le_rpow_pow (hN1 k) hM
    refine ⟨κ, hκ, hKκ, ?_, T, C, γ, j, cc, u, Q, R, A, F, ?_, hcount.trans hpow, hdisj,
      fun b => ?_, hmass⟩
    · rwa [hrp]
    · rwa [hrp]
    · refine chart_transfer (hcharts b) hpow ?_ ?_
      · rw [δ_rpow (hNpos k), hcc]
      · intro hfloor
        rwa [hfl k]

/-- The horizon is divided by the rescaling factor. -/
theorem H_rescale {c : ℝ} (hc : 0 < c) (hN1 : ∀ k, 1 ≤ N k) :
    H (fun k => N k ^ c) K (L / c) W ω ν E B (fun r => f (c * r) / c) =
      H N K L W ω ν E B f / c := by
  unfold H
  have hset : {h' : ℝ | term (fun k => N k ^ c) K (L / c) W ω ν E B
      (fun r => f (c * r) / c) h'} = c⁻¹ • {h : ℝ | term N K L W ω ν E B f h} := by
    ext h'
    rw [Set.mem_smul_set]
    simp only [Set.mem_ofPred_eq, smul_eq_mul]
    rw [term_rescale_iff hc hN1]
    constructor
    · intro ht
      exact ⟨c * h', ht, by field_simp⟩
    · rintro ⟨h, ht, rfl⟩
      rwa [show c * (c⁻¹ * h) = h by field_simp]
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul, div_eq_inv_mul]

/-- Every valid problem of length `L` has a valid length-one version (shift the index
so that `N ^ L ≥ 2`, then rescale the base by `L`), with horizon `H / L`, profile
`r ↦ f (L * r) / L` and the same `d, S, η`. -/
theorem prob_unit_length (hp : prob N K L d S η W ω ν E P B f g G) :
    ∃ k₀ : ℕ,
      prob (fun k => N (k + k₀) ^ L) (fun k => K (k + k₀)) 1 d S η (fun k => W (k + k₀))
        (fun k => ω (k + k₀)) (fun k => ν (k + k₀)) (fun k => E (k + k₀))
        (fun k => P (k + k₀)) (fun k => B (k + k₀)) (fun r => f (L * r) / L)
        (fun k γ r => g (k + k₀) γ (L * r)) (fun k γ u => G (k + k₀) γ (L * u)) ∧
      H (fun k => N (k + k₀) ^ L) (fun k => K (k + k₀)) 1 (fun k => W (k + k₀))
        (fun k => ω (k + k₀)) (fun k => ν (k + k₀)) (fun k => E (k + k₀))
        (fun k => B (k + k₀)) (fun r => f (L * r) / L) = H N K L W ω ν E B f / L := by
  have hL : 0 < L := hp.2.2.2.1
  have hN2 : ∀ k, 2 ≤ N k := hp.1
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (hp.2.1.eventually_ge_atTop ((2 : ℝ) ^ (1 / L)))
  refine ⟨k₀, ?_, ?_⟩
  · have hshift := prob_reindex hp (fun k => k + k₀) (tendsto_add_atTop_nat k₀)
    have hN' : ∀ k, 2 ≤ N (k + k₀) ^ L := by
      intro k
      have h1 := hk₀ (k + k₀) (by omega)
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / L)) ^ L := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hL.ne', Real.rpow_one]
        _ ≤ N (k + k₀) ^ L := Real.rpow_le_rpow (by positivity) h1 hL.le
    have h := prob_rescale hshift hL hN'
    rwa [div_self hL.ne'] at h
  · have hN1 : ∀ k, 1 ≤ N (k + k₀) := fun k => le_trans (by norm_num) (hN2 (k + k₀))
    have h := H_rescale (N := fun k => N (k + k₀)) (K := fun k => K (k + k₀))
      (L := L) (W := fun k => W (k + k₀)) (ω := fun k => ω (k + k₀))
      (ν := fun k => ν (k + k₀)) (E := fun k => E (k + k₀)) (B := fun k => B (k + k₀))
      (f := f) hL hN1
    rw [div_self hL.ne'] at h
    rw [h, H_shift]

end

end Submission.Lib.K4ExactProblemOps
