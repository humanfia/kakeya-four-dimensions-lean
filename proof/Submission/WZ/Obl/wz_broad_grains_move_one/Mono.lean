-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_move_one.Mono.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_move_one.Defs

/-!
# Error monotonicity of the frozen states

For `0 < d ≤ 1` and `h ≤ h'`, every clause of `A`, `C`, `H`, `Broad` and `J` that depends on
the error gets weaker when `h` is replaced by `h'`: `d ^ h' ≤ d ^ h` and `d ^ (-h) ≤ d ^ (-h')`.
The stopping conditions of `J` do not depend on the error.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_move_one

/-- `d ^ h' ≤ d ^ h` and `d ^ (-h) ≤ d ^ (-h')` for `0 < d ≤ 1`, `h ≤ h'`. -/
theorem rpow_err_le {d h h' : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h') :
    d ^ h' ≤ d ^ h ∧ d ^ (-h) ≤ d ^ (-h') :=
  ⟨Real.rpow_le_rpow_of_exponent_ge hd hd1 hh,
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hh)⟩

theorem A_mono {d h h' : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (ha : A d h (d ^ (-h)) (d ^ (-h)) n x v Y) :
    A d h' (d ^ (-h')) (d ^ (-h')) n x v Y := by
  obtain ⟨hp, hi⟩ := rpow_err_le hd hd1 hh
  obtain ⟨hn, ht, hx, hm, hk, hf⟩ := ha
  refine ⟨hn, ht, hx, le_trans ?_ hm, ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    have : (0 : ℝ) ≤ (n : ℝ) * d ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_right hp this
    simpa [mul_assoc] using h2
  · intro W hW
    exact (hk W hW).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hi) _)
  · intro u t r hu hr
    refine (hf u t r hu hr).trans (mul_le_mul_left ?_ _)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg n))

theorem C_mono {d h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hc : C d h n x v Y S Z ρ N y w f b) : C d h' n x v Y S Z ρ N y w f b := by
  obtain ⟨hp, hi⟩ := rpow_err_le hd hd1 hh
  obtain ⟨hz, hm, hw, ht, hf, hb, hbal, hx, hov⟩ := hc
  refine ⟨hz, le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hp) _) hm, hw, ht, ?_, hb,
    ?_, hx, ?_⟩
  · intro u t r hu hr
    refine (hf u t r hu hr).trans (mul_le_mul_left ?_ _)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg N))
  · intro k k'
    exact (hbal k k').trans (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _))
  · intro i hiS
    exact (hov i hiS).trans hi

theorem H_mono {d h h' ρ a c b g : ℝ} {n N : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hH : H d h n x v S Z ρ N y w f a c b g) : H d h' n x v S Z ρ N y w f a c b g := by
  obtain ⟨hp, -⟩ := rpow_err_le hd hd1 hh
  obtain ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmass, hmult, hcross,
    hb, hcount⟩ := hH
  have ha : 0 ≤ a := hd.le.trans hda
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  refine ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1, hgeom, hdisj, hunion, le_trans ?_ hmass, hmult,
    hcross, hb, hcount⟩
  apply ENNReal.ofReal_le_ofReal
  have h0 : (0 : ℝ) ≤ (L : ℝ) * a * (ρ * c) * c := by positivity
  have h2 := mul_le_mul_of_nonneg_right hp h0
  simpa [mul_assoc] using h2

theorem Broad_mono {ω ζ d h h' ρ : ℝ} {n N : ℕ} {v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hb : Broad ω ζ d h ρ n N v S Z f) : Broad ω ζ d h' ρ n N v S Z f := by
  obtain ⟨-, hi⟩ := rpow_err_le hd hd1 hh
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hd.trans_le hdr
  have hρ : 0 < ρ := hr.trans_le hrρ
  refine (hb k p u r hu hdr hrρ).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg (div_nonneg hr.le hρ.le) _)

/-- `J` with its witnesses made explicit. -/
theorem J_iff {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {j : ℕ} :
    J ω ζ d h ρ c n x v Y j ↔
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
        (a g : ℝ), C d h n x v Y S Z ρ N y w f True ∧ d ^ (1 - ω / 100) ≤ ρ ∧ 0 < g ∧
        Broad ω ζ d h ρ n N v S Z f ∧ H d h n x v S Z ρ N y w f a c 0 g ∧
        ((1 ≤ j → d ^ ζ * (ρ / d) * N / n ≤ c) ∧ (2 ≤ j → ρ ≤ d ^ (ω / 100)) ∧
          (3 ≤ j → g ≤ d ^ (-ζ))) :=
  Iff.rfl

theorem J_mono {ω ζ d h h' ρ c : ℝ} {n j : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hJ : J ω ζ d h ρ c n x v Y j) : J ω ζ d h' ρ c n x v Y j := by
  obtain ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hH, hstop⟩ := J_iff.1 hJ
  exact J_iff.2 ⟨S, Z, N, y, w, f, a, g, C_mono hd hd1 hh hc, hρ, hg,
    Broad_mono hd hd1 hh hbr, H_mono hd hd1 hh hH, hstop⟩

/-- Raising the stage index needs exactly the new stopping condition. -/
theorem J_zero_to_one {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
    (a g : ℝ) (hc : C d h n x v Y S Z ρ N y w f True) (hρ : d ^ (1 - ω / 100) ≤ ρ) (hg : 0 < g)
    (hbr : Broad ω ζ d h ρ n N v S Z f) (hH : H d h n x v S Z ρ N y w f a c 0 g)
    (hlen : d ^ ζ * (ρ / d) * N / n ≤ c) : J ω ζ d h ρ c n x v Y 1 :=
  J_iff.2 ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hH, fun _ => hlen,
    fun h2 => absurd h2 (by norm_num), fun h3 => absurd h3 (by norm_num)⟩

/-- A state at stage `0` from explicit witnesses. -/
theorem J_zero_of {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
    (a g : ℝ) (hc : C d h n x v Y S Z ρ N y w f True) (hρ : d ^ (1 - ω / 100) ≤ ρ) (hg : 0 < g)
    (hbr : Broad ω ζ d h ρ n N v S Z f) (hH : H d h n x v S Z ρ N y w f a c 0 g) :
    J ω ζ d h ρ c n x v Y 0 :=
  J_iff.2 ⟨S, Z, N, y, w, f, a, g, hc, hρ, hg, hbr, hH, fun h1 => absurd h1 (by norm_num),
    fun h2 => absurd h2 (by norm_num), fun h3 => absurd h3 (by norm_num)⟩

/-- The grains of `H` force `0 < c` and `ρ ≤ 1`. -/
theorem H_scales {d h ρ a c b g : ℝ} {n N : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N} (hd : 0 < d)
    (hH : H d h n x v S Z ρ N y w f a c b g) : 0 < c ∧ c ≤ 1 ∧ 0 < ρ ∧ ρ ≤ 1 := by
  obtain ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1, -⟩ := hH
  have ha : 0 < a := hd.trans_le hda
  have hrc : 0 < ρ * c := ha.trans_le hab
  have hc : 0 < c := hrc.trans_le hbc
  refine ⟨hc, hc1, pos_of_mul_pos_left hrc hc.le, ?_⟩
  have : ρ * c ≤ 1 * c := by simpa using hbc
  exact le_of_mul_le_mul_right this hc

/-- The small-power length lower bound suffices for the length-progress alternative. -/
theorem length_progress {d ζ e c c' r : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (he : e ≤ ζ / 2)
    (hr : 0 ≤ r) (hshort : c < d ^ ζ * r) (hnew : d ^ e * r ≤ c') : d ^ (-ζ / 2) * c ≤ c' := by
  calc d ^ (-ζ / 2) * c ≤ d ^ (-ζ / 2) * (d ^ ζ * r) :=
        mul_le_mul_of_nonneg_left hshort.le (Real.rpow_nonneg hd.le _)
    _ = d ^ (ζ / 2) * r := by
        rw [← mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
    _ ≤ d ^ e * r := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 he) hr
    _ ≤ c' := hnew

end WangZahlLot.Obl.wz_broad_grains_move_one
