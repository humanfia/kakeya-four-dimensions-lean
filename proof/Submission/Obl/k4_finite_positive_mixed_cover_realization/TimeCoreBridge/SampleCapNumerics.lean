-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SampleCapNumerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleProjectionControl
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.EntryGeometryBudget
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupFloorBounds
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.OriginalMassTransport

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}


/-- The common original cap, multiplied by the entire packet-relative entry
count, is charged to the full old prior and its time length. All sheet-scale
powers cancel against the comparison volume. -/
theorem sampleInput_entry_cap_budget
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {Abound : ℝ} {Cs : ℕ} (hA : 0 < Abound)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Abound ^ (Cs : ℝ)))
    (hK : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1) (b : Fin C) (hlev : lev b = i) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
    let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
    let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
    let prior := (ν (γ b) (A b)).toReal / (2 : ℝ) ^ T i
    let Hbase := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) *
      sheetRadius Abound Cs ^ 3 * |(Q b).det| / (2 : ℝ) ^ T i
    0 < prior ∧ 0 < Hbase ∧
      Nk ^ exponent * geom * Hbase ≤ prior * ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) * Nk ^ loss := by
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hκ : 0 < κ := zero_lt_one.trans_le hpath.1
  obtain ⟨hscalar, hi, hgh, _, _, hmargin, _, hentry, _, _, _, _, hq0, hqL, hqlo, hqhi⟩ := hsi
  have hc := (hpath.2.2.2.2.2.2.2 b).2.2
  rw [hlev] at hc
  have hJ : 0 < |(Q b).det| := abs_pos.mpr hc.1
  have hlen : 0 < (2 : ℝ) ^ T i := by positivity
  letI := (hscalar.2.2.2 (γ b)).1
  have hprior := path_packet_prior_floor hNkpos hpath b hlev
  have hp : Nk ^ (-f (r i)) * |(Q b).det| / κ ≤
      (ν (γ b) (A b)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hprior
  have hp0 : 0 < (ν (γ b) (A b)).toReal := (by positivity :
    0 < Nk ^ (-f (r i)) * |(Q b).det| / κ).trans_le hp
  have hri : 0 < r i := (hpath.2.2.2.2.1 i hi).2.1
  have hh : 0 < h := hgain.trans_le hgh
  have hriL : r i ≤ L := by nlinarith [mul_pos hh hL]
  have hprofile := (menuDepth_profile_increment hL.le hd₁ hd₁1 hδ₀ ⟨hri.le, hriL⟩ ⟨hq0, hqL⟩
    (fun z hz => hlin z hz.1 hz.2) hqlo hqhi).1
  have hfit : 0 ≤ 4 * ρ * gain * L + 4 * ε := by positivity
  have hcap := candidate_cap_uniform_budget
    (n := Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε))
    (τ := ((2 : ℝ) ^ T i)⁻¹) (τtail := τ)
    hNk (by positivity) le_rfl hfit (by positivity) hJ.le hκ hp0.le hp hprofile
  have hgeom := entry_geometry_volume_budget hA hpath.1 hs hK
  have hradius : 0 < sheetRadius Abound Cs := by unfold sheetRadius; positivity
  dsimp only
  refine ⟨by positivity, by positivity, ?_⟩
  calc
    _ = (Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε) *
        (Nk ^ (-f q + τ) * (16 * (1 + (Nk ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) *
          (((2 : ℝ) ^ T i)⁻¹ * |(Q b).det|))) *
          (((2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4) * sheetRadius Abound Cs ^ 3) := by ring
    _ ≤ ((((2 : ℝ) ^ T i)⁻¹ * (ν (γ b) (A b)).toReal) * (32 * κ) *
        Nk ^ ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)) * ((2 : ℝ) ^ (18 : ℕ) * κ ^ 5) := by
      exact mul_le_mul hcap hgeom (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual packet-relative heavy threshold has a uniform comparison
projection fraction, including arbitrary positive world weights. -/
theorem sampleInput_entry_projection_fraction
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {Abound : ℝ} {Cs : ℕ} (hA : 0 < Abound)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Abound ^ (Cs : ℝ)))
    (hK : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1) (a : Fin n)
    (hω : 0 < ω (γ (old a))) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
    let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
    let prior := (ν (γ (old a)) (A (old a))).toReal / (2 : ℝ) ^ T i
    let Hbase := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) *
      sheetRadius Abound Cs ^ 3 * |(Q (old a)).det| / (2 : ℝ) ^ T i
    groupFloor Nk (slackTot ρ gain L ε σ τ) ≤
      ((ω (γ (old a)) * prior) * Nk ^ (-exponent - ε - τ) / geom) /
        (ω (γ (old a)) * Hbase) := by
  let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
  let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
  let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
  let prior := (ν (γ (old a)) (A (old a))).toReal / (2 : ℝ) ^ T i
  let Hbase := Nk ^ (-f q + τ) * (16 * (1 + (Nk ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) *
    sheetRadius Abound Cs ^ 3 * |(Q (old a)).det| / (2 : ℝ) ^ T i
  have hc := sampleInput_entry_cap_budget hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hsi hpath hlin hA hs hK (old a) (hsi.2.2.2.2.2.2.2.1 a).1
  change 0 < prior ∧ 0 < Hbase ∧
    Nk ^ exponent * geom * Hbase ≤ prior * ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) * Nk ^ loss at hc
  obtain ⟨hp, hH, hbudget⟩ := hc
  have hgeom : 0 < geom := by dsimp [geom]; positivity
  have hκpos : 0 < κ := zero_lt_one.trans_le hpath.1
  have hC : 0 < (2 : ℝ) ^ (23 : ℕ) * κ ^ 6 := by positivity
  have hwBudget : Nk ^ exponent * geom * (ω (γ (old a)) * Hbase) ≤
      (ω (γ (old a)) * prior) * ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) * Nk ^ loss := by
    convert mul_le_mul_of_nonneg_left hbudget hω.le using 1 <;> ring
  have hratio := relative_entry_floor_of_cap_budget (slack := ε + τ)
    (zero_lt_one.trans_le hNk) (mul_pos hω hp) hgeom (mul_pos hω hH) hC hwBudget
  have hfloor := groupFloor_le_original_fraction hNk hpath.1 hpath.2.1 hσ hρ hgain.le hL.le hε hτ hδρ
  dsimp only
  change groupFloor Nk (slackTot ρ gain L ε σ τ) ≤
    ((ω (γ (old a)) * prior) * Nk ^ (-exponent - ε - τ) / geom) / (ω (γ (old a)) * Hbase)
  apply hfloor.trans
  convert hratio using 1 <;> congr 2 <;> ring

/-- The original heavy-entry threshold implies the positive uniform mass floor
used by group recovery, including the original world weight. -/
theorem sampleInput_heavy_entry_floor
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {Abound : ℝ} {Cs : ℕ} (hA : 0 < Abound)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Abound ^ (Cs : ℝ)))
    (hK : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1) (a : Fin n)
    (hω : 0 < ω (γ (old a))) (mass : ENNReal)
    (hfloor : (ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ (old a)) (A (old a))) *
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L + 4 * ε) - ε - τ) /
        ((2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4)) ≤ mass) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let Hbase := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) *
      sheetRadius Abound Cs ^ 3 * |(Q (old a)).det| / (2 : ℝ) ^ T i
    ENNReal.ofReal ((ω (γ (old a)) * Hbase) * groupFloor Nk (slackTot ρ gain L ε σ τ)) ≤
      ENNReal.ofReal (ω (γ (old a))) * mass := by
  let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
  let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
  let prior := (ν (γ (old a)) (A (old a))).toReal / (2 : ℝ) ^ T i
  let Hbase := Nk ^ (-f q + τ) * (16 * (1 + (Nk ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) *
    sheetRadius Abound Cs ^ 3 * |(Q (old a)).det| / (2 : ℝ) ^ T i
  letI := (hsi.1.2.2.2 (γ (old a))).1
  have hsc : ENNReal.ofReal prior =
      ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ (old a)) (A (old a)) := by
    dsimp only [prior]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact mul_comm _ _
  have hc := sampleInput_entry_cap_budget hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hsi hpath hlin hA hs hK
    (old a) (hsi.2.2.2.2.2.2.2.1 a).1
  have hHbase : 0 < Hbase := hc.2.1
  have hratio := sampleInput_entry_projection_fraction hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hσ hτ hδρ
    hsi hpath hlin hA hs hK a hω
  change groupFloor Nk (slackTot ρ gain L ε σ τ) ≤
    ((ω (γ (old a)) * prior) * Nk ^ (-exponent - ε - τ) / geom) / (ω (γ (old a)) * Hbase) at hratio
  dsimp only
  exact weighted_mass_floor_of_ratio hω hHbase (by dsimp only [prior]; positivity)
    hsc hratio hfloor

end
end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
