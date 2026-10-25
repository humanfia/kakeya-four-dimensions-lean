import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueBinGeometry
import Submission.Obl.k4_general_wide_layer_offset_comparison.ShortTimeCodes

/-!
# Short domain codes met by one true label and one major bin

A true label `Q` at depth `r`, together with an original major bin `tag`
(intercept and velocity of `Z` at width `χ = N^(-m)`), meets only boundedly
many short domain codes `(time block, Y'-bin at width g, Y-bin at width q*g)`.
The bound depends only on `K`.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set

noncomputable section

/-- Two reals within `M * δ` of each other have floors at scale `δ` within
`⌈M⌉₊ + 1` of each other. -/
theorem floor_div_mem_Icc {x y δ M : ℝ} (hδ : 0 < δ) (hxy : |x - y| ≤ M * δ) :
    ⌊x / δ⌋ ∈ Finset.Icc (⌊y / δ⌋ - ((⌈M⌉₊ : ℤ) + 1)) (⌊y / δ⌋ + ((⌈M⌉₊ : ℤ) + 1)) := by
  have hM : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have hdiv : |x / δ - y / δ| ≤ (⌈M⌉₊ : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    exact hxy.trans (mul_le_mul_of_nonneg_right hM hδ.le)
  rw [abs_le] at hdiv
  have hx1 := Int.floor_le (x / δ)
  have hx2 := Int.lt_floor_add_one (x / δ)
  have hy1 := Int.floor_le (y / δ)
  have hy2 := Int.lt_floor_add_one (y / δ)
  rw [Finset.mem_Icc]
  constructor
  · have h : ((⌊y / δ⌋ - ((⌈M⌉₊ : ℤ) + 1) : ℤ) : ℝ) < (⌊x / δ⌋ : ℝ) + 1 := by
      push_cast
      linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast h)
  · have h : (⌊x / δ⌋ : ℝ) < ((⌊y / δ⌋ + ((⌈M⌉₊ : ℤ) + 1) : ℤ) : ℝ) + 1 := by
      push_cast
      linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast h)

theorem card_Icc_sym (c : ℤ) (w : ℕ) :
    ((Finset.Icc (c - ((w : ℤ) + 1)) (c + ((w : ℤ) + 1))).card : ℝ) = 2 * w + 3 := by
  rw [Int.card_Icc]
  have h : c + ((w : ℤ) + 1) + 1 - (c - ((w : ℤ) + 1)) = 2 * (w : ℤ) + 3 := by ring
  rw [h]
  have h' : (2 * (w : ℤ) + 3).toNat = 2 * w + 3 := by omega
  rw [h']
  push_cast
  ring

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The finite menu of short domain codes for a true label and a major bin.
Its three ranges come from the true time block, the true transverse slope
row and the true transverse affine row, evaluated on the major bin. -/
def trueDomains (k : ℕ) (r m : ℝ) (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g := p.N k ^ (-p.ℓ * r)
  let χ := p.N k ^ (-m)
  let t₀ := ((p.j k r Q : ℕ) : ℝ) * q
  let cv := p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * χ)
  let cy := p.c k r Q 2 + p.c k r Q 4 * ((tag 1 : ℝ) * χ) + t₀ * cv
  ({((p.j k r Q : ℕ) : ℤ)} : Finset ℤ) ×ˢ
    (Finset.Icc (⌊cv / g⌋ - ((⌈2 * p.K k⌉₊ : ℤ) + 1)) (⌊cv / g⌋ + ((⌈2 * p.K k⌉₊ : ℤ) + 1)) ×ˢ
      Finset.Icc (⌊cy / (q * g)⌋ - ((⌈3 * p.K k⌉₊ : ℤ) + 1))
        (⌊cy / (q * g)⌋ + ((⌈3 * p.K k⌉₊ : ℤ) + 1)))

theorem card_trueDomains_le (k : ℕ) (r m : ℝ) (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ)
    (hK : 0 ≤ p.K k) :
    ((p.trueDomains k r m Q tag).card : ℝ) ≤ (4 * p.K k + 5) * (6 * p.K k + 5) := by
  simp only [trueDomains, Finset.card_product, Finset.card_singleton, one_mul]
  push_cast
  rw [card_Icc_sym, card_Icc_sym]
  have h1 : ((⌈2 * p.K k⌉₊ : ℕ) : ℝ) ≤ 2 * p.K k + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : ((⌈3 * p.K k⌉₊ : ℕ) : ℝ) ≤ 3 * p.K k + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have h1' : 0 ≤ 2 * ((⌈2 * p.K k⌉₊ : ℕ) : ℝ) + 3 := by positivity
  calc
    (2 * ((⌈2 * p.K k⌉₊ : ℕ) : ℝ) + 3) * (2 * ((⌈3 * p.K k⌉₊ : ℕ) : ℝ) + 3) ≤
        (2 * (2 * p.K k + 1) + 3) * (2 * (3 * p.K k + 1) + 3) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = (4 * p.K k + 5) * (6 * p.K k + 5) := by ring

/-- Every original incidence of a true label, read in its own dyadic block
with its own major bin, has its short domain code in the true menu. -/
theorem AtDepth.domainCode_mem_trueDomains {k : ℕ} {r m R : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hK : 0 ≤ p.K k)
    (hχwidth : p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hχslope : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r))
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {ω : α × ℝ}
    (hl : ω.1 ∈ p.A k r Q)
    (hz : ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1)
    (hv : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0)
    (htime : ⌊ω.2 / (2 : ℝ) ^ (-(p.T k r : ℤ))⌋ = ((p.j k r Q : ℕ) : ℤ)) :
    p.domainCode k ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
      ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) ω ∈ p.trueDomains k r m Q tag := by
  set q := (2 : ℝ) ^ (-(p.T k r : ℤ)) with hq_def
  set g := p.N k ^ (-p.ℓ * r) with hg_def
  set χ := p.N k ^ (-m) with hχ_def
  have hq : 0 < q := by rw [hq_def]; positivity
  have hg : 0 < g := by rw [hg_def]; positivity
  have hχ : 0 < χ := by rw [hχ_def]; positivity
  set t₀ := ((p.j k r Q : ℕ) : ℝ) * q with ht₀_def
  have ht₀ : t₀ ∈ block (p.T k r) (p.j k r Q) := by
    have hpow : (2 : ℝ) ^ (p.T k r) = q⁻¹ := by
      rw [hq_def, zpow_neg, zpow_natCast, inv_inv]
    change ((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ (p.T k r) ≤ t₀ ∧
      t₀ ≤ (((p.j k r Q : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (p.T k r)
    rw [hpow, div_inv_eq_mul, div_inv_eq_mul, ht₀_def]
    constructor
    · exact le_rfl
    · nlinarith
  have hband := AtDepth.transverse_band_on_major_bin p hat hK hχ hχwidth hχslope Q hl
    (tag 1) (tag 0) hz hv ht₀
  simp only [trueDomains, domainCode, movingDomainCode]
  rw [← hq_def, ← hg_def, ← hχ_def]
  simp only [Finset.mem_product, Finset.mem_singleton]
  refine ⟨htime, ?_, ?_⟩
  · apply floor_div_mem_Icc hg
    calc
      _ ≤ (2 * p.K k) * g := hband.2
      _ ≤ _ := le_rfl
  · rw [htime]
    apply floor_div_mem_Icc (mul_pos hq hg)
    have hx : (p.x k ω.1 t₀) 2 = p.b k ω.1 1 + t₀ * p.b k ω.1 4 := rfl
    have h1 := hband.1
    rw [hx] at h1
    calc
      |p.b k ω.1 1 + ((p.j k r Q : ℕ) : ℤ) * q * p.b k ω.1 4 -
          (p.c k r Q 2 + p.c k r Q 4 * ((tag 1 : ℝ) * χ) +
            t₀ * (p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * χ)))| =
          |p.b k ω.1 1 + t₀ * p.b k ω.1 4 - (p.c k r Q 2 + p.c k r Q 4 * ((tag 1 : ℝ) * χ)) -
            t₀ * (p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * χ))| := by
        congr 1
        rw [ht₀_def]
        push_cast
        ring
      _ ≤ (3 * p.K k) * (q * g) := h1

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
