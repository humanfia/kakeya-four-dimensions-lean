import Submission.Obl.k4_clean_cover_graph_atlas.SampleCapNumerics
import Submission.Obl.k4_clean_cover_graph_atlas.FinitePacketSums

namespace Submission.Obl.k4_clean_cover_graph_atlas
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


open Classical in
/-- Positive common group caps, with their entire active sum charged to the
unchanged original prior budget. -/
theorem sampleInput_common_caps_sum
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hgain : 0 < gain)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hρ : 0 ≤ ρ) (hδ₀ : 0 ≤ δ₀) (hε : 0 ≤ ε)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hlin : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L)
    {Abound : ℝ} {Cs : ℕ} (hA : 0 < Abound)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * Abound ^ (Cs : ℝ)))
    (hK : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hω : ∀ e, (cov e).Nonempty → 0 < ω (γ (old e.1))) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
    let cap := fun b : Fin C => Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) *
      sheetRadius Abound Cs ^ 3 * |(Q b).det| / (2 : ℝ) ^ T i
    ∃ H : Group C s₀ K → ℝ, (∀ G, 0 < H G) ∧
      (∀ e, (cov e).Nonempty → H (entryGroup old e) = ω (γ (old e.1)) * cap (old e.1)) ∧
      (∑ e, if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (23 : ℕ) * Nk ^ (loss + 6 * σ)) := by
  classical
  let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
  let loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ
  let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
  let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
  let cap := fun b : Fin C => Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) *
    sheetRadius Abound Cs ^ 3 * |(Q b).det| / (2 : ℝ) ^ T i
  let prior := fun b : Fin C => (ν (γ b) (A b)).toReal / (2 : ℝ) ^ T i
  let Kraw := (2 : ℝ) ^ (23 : ℕ) * κ ^ 6 * Nk ^ loss
  let packet : Entry n s₀ K → {b : Fin C // lev b = i} := fun e =>
    ⟨old e.1, (hsi.2.2.2.2.2.2.2.1 e.1).1⟩
  let weight := fun b : {b : Fin C // lev b = i} => ENNReal.ofReal (ω (γ b.val))
  let scale := fun b : {b : Fin C // lev b = i} =>
    ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ b.val) (A b.val)
  let H := fun G : Group C s₀ K => if 0 < ω (γ G.1) then ω (γ G.1) * cap G.1 else 1
  have hNpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hradius : 0 < sheetRadius Abound Cs := by unfold sheetRadius; positivity
  have hcapPos : ∀ b, 0 < cap b := by
    intro b
    have hQ := ((hpath.2.2.2.2.2.2.2 b).2.2).1
    have hJ : 0 < |(Q b).det| := abs_pos.mpr hQ
    dsimp only [cap]
    positivity
  have hH : ∀ G, 0 < H G := by
    intro G
    dsimp only [H]
    split_ifs with hw
    · exact mul_pos hw (hcapPos _)
    · norm_num
  have heq : ∀ e, (cov e).Nonempty → H (entryGroup old e) = ω (γ (old e.1)) * cap (old e.1) := by
    intro e he
    exact if_pos (hω e he)
  have hpacketCap : ∀ b, ((Finset.univ.filter (fun e => packet e = b)).card : ENNReal) *
      ENNReal.ofReal (cap b.val) ≤ ENNReal.ofReal Kraw * scale b := by
    intro b
    letI := (hsi.1.2.2.2 (γ b.val)).1
    have hsc : ENNReal.ofReal (prior b.val) = scale b := by
      dsimp only [prior, scale]
      rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact mul_comm _ _
    have hfilter : Finset.univ.filter (fun e : Entry n s₀ K => packet e = b) =
        Finset.univ.filter (fun e : Entry n s₀ K => old e.1 = b.val) := by
      ext e
      simp [packet, Subtype.ext_iff]
    have hcard := card_Entry_packet_le (s₀ := s₀) (K := K) old b.val
      (hsi.2.2.2.2.2.2.2.2.2.1 b.val)
    have hcard' : ((Finset.univ.filter (fun e : Entry n s₀ K => packet e = b)).card : ℝ) ≤
        Nk ^ exponent * geom := by
      rw [hfilter]
      simpa only [exponent, geom, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcard
    have hc := sampleInput_entry_cap_budget hNk hL hgain hd₁ hd₁1 hρ hδ₀ hε hsi hpath hlin hA hs hK
      b.val b.property
    change 0 < prior b.val ∧ 0 < cap b.val ∧
      Nk ^ exponent * geom * cap b.val ≤ prior b.val * ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) * Nk ^ loss at hc
    have hreal : ((Finset.univ.filter (fun e : Entry n s₀ K => packet e = b)).card : ℝ) * cap b.val ≤
        prior b.val * Kraw := by
      apply ((mul_le_mul_of_nonneg_right hcard' (hcapPos b.val).le).trans hc.2.2).trans_eq
      dsimp only [Kraw]
      ring
    calc
      _ = ENNReal.ofReal (((Finset.univ.filter (fun e : Entry n s₀ K => packet e = b)).card : ℝ) *
          cap b.val) := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (prior b.val * Kraw) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (by dsimp [prior]; positivity), hsc]
        ring
  have hbudget : (∑ b, weight b * scale b) ≤ 1 := path_level_prior_budget hsi.1 hpath i
  have hsum := packet_constant_sum_le packet weight (fun b => ENNReal.ofReal (cap b.val)) scale
    (ENNReal.ofReal Kraw) hpacketCap hbudget
  have hpoint (e : Entry n s₀ K) :
      (if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0) ≤
        weight (packet e) * ENNReal.ofReal (cap (old e.1)) := by
    by_cases he : (cov e).Nonempty
    · rw [if_pos he, heq e he, ENNReal.ofReal_mul (hsi.1.2.1 _)]
    · rw [if_neg he]
      exact zero_le
  have hκ6 : κ ^ 6 ≤ Nk ^ (6 * σ) := by
    calc
      _ ≤ (Nk ^ σ) ^ (6 : ℕ) := pow_le_pow_left₀ (zero_le_one.trans hpath.1) hpath.2.1 _
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
  have hKraw : Kraw ≤ (2 : ℝ) ^ (23 : ℕ) * Nk ^ (loss + 6 * σ) := by
    dsimp only [Kraw]
    calc
      _ ≤ ((2 : ℝ) ^ (23 : ℕ) * Nk ^ (6 * σ)) * Nk ^ loss := by gcongr
      _ = _ := by rw [Real.rpow_add hNpos loss (6 * σ)]; ring
  dsimp only
  refine ⟨H, hH, heq, ?_⟩
  exact (Finset.sum_le_sum (fun e _ => hpoint e)).trans (hsum.trans (ENNReal.ofReal_le_ofReal hKraw))

end
end Submission.Obl.k4_clean_cover_graph_atlas
