-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_terminal_grains_restoration.Grains
import Submission.WZ.Obl.wz_terminal_grains_restoration.Analysis
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TerminalCount

/-!
# Terminal grains restoration: the argument

Given `h > 0`, take `ζ = min (ω/1000) h`, apply the refinement principle `R` with
`β = ω ζ / 100` and `τ = h/4`, and take `η ≤ min (η_R, h/12, 1)`. On a terminal `D`-state,
`R` gives a gain or a refinement `S' ⊆ S`, `Z' ⊆ Z` keeping a `δ^τ` share of the mass with the
below-slab bound. The dyadic selection (`select`) keeps whole coarse fibres of comparable size
and a common multiplicity class, losing `(log₂ n + 1)² ≤ δ^(-h/4)`; the retained coarse tubes
are reindexed (`restore_cover`), and the old grains over them are cut down to the new fibre
unions (`restore_grains`). The count of retained coarse tubes is bounded below through the
normalized balance of the old fibres and the tube volume bound `56 δ²`.
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory Finset
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem rpow_neg_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    δ ^ (-a) ≤ δ ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

theorem rpow_mono' {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    δ ^ b ≤ δ ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hab

theorem Fp_mono {ρ l l' : ℝ} {N : ℕ} {y w : Fin N → Space} (hF : Fp ρ l N y w) (hl : l ≤ l') :
    Fp ρ l' N y w := by
  intro u t r hu hr
  refine (hF u t r hu hr).trans ?_
  gcongr

theorem Kp_mono {d m m' : ℝ} {n : ℕ} {x v : Fin n → Space} (hK : Kp d m n x v) (hm : m ≤ m') :
    Kp d m' n x v := by
  intro W hW
  refine (hK W hW).trans ?_
  gcongr

theorem Ap_mono {δ η η' : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηη : η ≤ η')
    (hA : Ap δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) : Ap δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
  obtain ⟨hn, hi, hX, hmass, hK, hF⟩ := hA
  refine ⟨hn, hi, hX, ?_, Kp_mono hK (rpow_neg_mono hδ hδ1 hηη),
    Fp_mono hF (rpow_neg_mono hδ hδ1 hηη)⟩
  refine le_trans ?_ hmass
  apply ENNReal.ofReal_le_ofReal
  have h1 := rpow_mono' hδ hδ1 hηη
  have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hn') (by positivity)

theorem Cp_mono {δ η η' ρ : ℝ} {n N : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {S : Finset (Fin n)} {Z : Fin n → Set Space} {y w : Fin N → Space} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηη : η ≤ η')
    (hC : Cp δ η n x v Y S Z ρ N y w f True) : Cp δ η' n x v Y S Z ρ N y w f True := by
  obtain ⟨hZ, hmass, hw, hT, hF, hb, hbal, hX, hcount⟩ := hC
  unfold Cp
  refine ⟨hZ, ?_, hw, hT, Fp_mono hF (rpow_neg_mono hδ hδ1 hηη), hb, ?_, hX, ?_⟩
  · refine le_trans ?_ hmass
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (rpow_mono' hδ hδ1 hηη)) le_rfl
  · intro k k'
    refine (hbal k k').trans ?_
    exact mul_le_mul_of_nonneg_right (rpow_neg_mono hδ hδ1 hηη) (qc_nonneg _)
  · intro i hi
    exact (hcount i hi).trans (rpow_neg_mono hδ hδ1 hηη)

theorem Broad_mono {δ ρ l l' β : ℝ} {n N : ℕ} {v : Fin n → Space} {S : Finset (Fin n)}
    {Z : Fin n → Set Space} {f : Fin n → Fin N} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hB : Broad δ ρ l β n N v S Z f) (hl : l ≤ l') : Broad δ ρ l' β n N v S Z f := by
  intro k p u r hu hr hrρ
  refine (hB k p u r hu hr hrρ).trans ?_
  have hr0 : 0 ≤ (r / ρ) ^ β := Real.rpow_nonneg (div_nonneg (by linarith) hρ.le) β
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hr0) (qc_nonneg _)

/-- `K` on the unit ball bounds the number of tubes. -/
theorem n_bound {δ η : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη1 : η ≤ 1)
    (hA : Ap δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) :
    (n : ℝ) ≤ (volume (Metric.ball (0:Space) 1)).toReal * δ ^ (-(3:ℝ)) := by
  obtain ⟨-, hi, -, -, hK, -⟩ := hA
  have h1 := hK (Metric.ball (0:Space) 1) (convex_ball 0 1)
  have hset : {i | Tb δ (x i) (v i) ⊆ Metric.ball (0:Space) 1} = Set.univ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (hi i).2.1
  rw [hset] at h1
  have hq : qc n Set.univ = n := by
    unfold qc
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hq] at h1
  set C₀ := (volume (Metric.ball (0:Space) 1)).toReal with hC₀
  have hvol : volume (Metric.ball (0:Space) 1) = ENNReal.ofReal C₀ :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hC₀0 : 0 ≤ C₀ := ENNReal.toReal_nonneg
  rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at h1
  have h2 : (n:ℝ) * δ ^ 2 ≤ δ ^ (-η) * C₀ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have h3 : δ ^ (-η) ≤ δ ^ (-(1:ℝ)) := rpow_neg_mono hδ hδ1 hη1
  have h4 : δ ^ (-(3:ℝ)) = δ ^ (-(1:ℝ)) / δ ^ 2 := by
    rw [show (-(3:ℝ)) = -(1:ℝ) + -(2:ℝ) by norm_num, Real.rpow_add hδ,
      Real.rpow_neg hδ.le (2:ℝ), Real.rpow_two, div_eq_mul_inv]
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [h4, mul_div_assoc', le_div_iff₀ hδ2]
  calc (n:ℝ) * δ ^ 2 ≤ δ ^ (-η) * C₀ := h2
    _ ≤ δ ^ (-(1:ℝ)) * C₀ := mul_le_mul_of_nonneg_right h3 hC₀0
    _ = C₀ * δ ^ (-(1:ℝ)) := by ring

/-- The arithmetic of the lower bound on the number of retained coarse tubes. -/
theorem budget_arith {δ h η n N s₁ Rc : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n) (hN : 0 ≤ N)
    (hηh : η ≤ h / 12) (hη : 0 < η) (h56 : 56 ≤ δ ^ (-(h / 4)))
    (hmass : δ ^ (h / 2) * (δ ^ η * n * δ ^ 2) ≤ s₁ * (56 * δ ^ 2))
    (hcard : s₁ * N ≤ Rc * (δ ^ (-η) * n)) :
    δ ^ (-η) * N ≤ δ ^ (-h) * Rc := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hA : 0 < δ ^ (h / 2) := Real.rpow_pos_of_pos hδ _
  have hu : 0 < δ ^ η := Real.rpow_pos_of_pos hδ _
  have hh : 0 < h := by linarith
  -- δ^(h/2) δ^η n ≤ 56 s₁
  have m1 : δ ^ (h / 2) * δ ^ η * n ≤ 56 * s₁ := by
    have : (δ ^ (h / 2) * δ ^ η * n) * δ ^ 2 ≤ (56 * s₁) * δ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hδ2
  -- s₁ N δ^η ≤ Rc n
  have hinv : δ ^ (-η) * δ ^ η = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  have m2 : s₁ * N * δ ^ η ≤ Rc * n := by
    have := mul_le_mul_of_nonneg_right hcard hu.le
    calc s₁ * N * δ ^ η ≤ Rc * (δ ^ (-η) * n) * δ ^ η := this
      _ = Rc * n * (δ ^ (-η) * δ ^ η) := by ring
      _ = Rc * n := by rw [hinv, mul_one]
  -- δ^(h/2) δ^(2η) N ≤ 56 Rc
  have hs₁ : 0 ≤ s₁ := by
    by_contra hneg
    push Not at hneg
    have : δ ^ (h / 2) * δ ^ η * n > 0 := by positivity
    linarith
  have m3 : δ ^ (h / 2) * δ ^ (2 * η) * N ≤ 56 * Rc := by
    have e : δ ^ (2 * η) = δ ^ η * δ ^ η := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    have key : (δ ^ (h / 2) * δ ^ (2 * η) * N) * n ≤ (56 * Rc) * n := by
      calc (δ ^ (h / 2) * δ ^ (2 * η) * N) * n = (δ ^ (h / 2) * δ ^ η * n) * (N * δ ^ η) := by
            rw [e]; ring
        _ ≤ (56 * s₁) * (N * δ ^ η) := mul_le_mul_of_nonneg_right m1 (by positivity)
        _ = 56 * (s₁ * N * δ ^ η) := by ring
        _ ≤ 56 * (Rc * n) := by linarith
        _ = (56 * Rc) * n := by ring
    exact le_of_mul_le_mul_right key hn
  -- N δ^h ≤ Rc δ^η
  have e1 : δ ^ h = δ ^ (h / 2) * δ ^ (2 * η) * δ ^ (h / 2 - 2 * η) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
  have e2 : δ ^ (h / 2 - 2 * η) = δ ^ η * δ ^ (h / 2 - 3 * η) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hsmall : 56 * δ ^ (h / 2 - 3 * η) ≤ 1 := by
    have h1 : δ ^ (h / 2 - 3 * η) ≤ δ ^ (h / 4) := rpow_mono' hδ hδ1 (by linarith)
    have h2 : δ ^ (-(h / 4)) * δ ^ (h / 4) = 1 := by
      rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
    have h3 : 0 < δ ^ (h / 4) := Real.rpow_pos_of_pos hδ _
    nlinarith
  have hRc : 0 ≤ Rc := by
    have : 0 ≤ δ ^ (h / 2) * δ ^ (2 * η) * N := by
      have := Real.rpow_pos_of_pos hδ (2 * η); positivity
    linarith
  have m4 : N * δ ^ h ≤ Rc * δ ^ η := by
    have hX : 0 ≤ δ ^ (h / 2 - 3 * η) := Real.rpow_nonneg hδ.le _
    calc N * δ ^ h = (δ ^ (h / 2) * δ ^ (2 * η) * N) * δ ^ η * δ ^ (h / 2 - 3 * η) := by
          rw [e1, e2]; ring
      _ ≤ (56 * Rc) * δ ^ η * δ ^ (h / 2 - 3 * η) := by gcongr
      _ = Rc * δ ^ η * (56 * δ ^ (h / 2 - 3 * η)) := by ring
      _ ≤ Rc * δ ^ η * 1 := by gcongr
      _ = Rc * δ ^ η := mul_one _
  have hhpos : 0 < δ ^ h := Real.rpow_pos_of_pos hδ _
  rw [Real.rpow_neg hδ.le, Real.rpow_neg hδ.le, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ hu hhpos]
  exact m4

theorem main (σ ω : ℝ) (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hR : ∀ β : ℝ, 0 < β → ∀ τ : ℝ, 0 < τ → Rp σ ω β τ) (h : ℝ) (hh : 0 < h) :
    ∃ ζ α κ η d₀ : ℝ, 0 < ζ ∧ ζ ≤ ω/1000 ∧ 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ h ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Ap δ η (δ^(-η)) (δ^(-η)) n x v Y → ∀ ρ c : ℝ, Dp ω ζ δ η ρ c n x v Y true →
        Gain σ ω α κ δ n Y ∨
          ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → Space)
            (f : Fin n → Fin N), Gp ω δ h n x v Y S Z ρ N y w f := by
  classical
  set ζ := min (ω / 1000) h with hζdef
  have hζpos : 0 < ζ := lt_min (by linarith) hh
  have hζω : ζ ≤ ω / 1000 := min_le_left _ _
  have hζh : ζ ≤ h := min_le_right _ _
  have hβ : 0 < ω * ζ / 100 := by positivity
  obtain ⟨α, κ, ηR, dR, hα, hκ, hηR, hηRτ, hdR, hdR1, hRp⟩ :=
    hR (ω * ζ / 100) hβ (h / 4) (by positivity)
  set η := min ηR (min (h / 12) 1) with hηdef
  have hηpos : 0 < η := lt_min hηR (lt_min (by positivity) one_pos)
  have hηηR : η ≤ ηR := min_le_left _ _
  have hηh12 : η ≤ h / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨d₁, hd₁, hd₁1, hd₁prop⟩ :=
    log_class_bound hh (volume (Metric.ball (0:Space) 1)).toReal
  obtain ⟨d₂, hd₂, hd₂1, hd₂prop⟩ := const_le_rpow_neg (ε := h / 4) (by positivity) 56
  refine ⟨ζ, α, κ, η, min (min dR d₁) (min d₂ (1/100)), hζpos, hζω, hα, hκ, hηpos,
    by linarith, lt_min (lt_min hdR hd₁) (lt_min hd₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro δ hδ hδd n x v Y hA ρ c hD
  have hδR : δ ≤ dR := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₁ : δ ≤ d₁ := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ₁.trans hd₁1
  have h56 : (56:ℝ) ≤ δ ^ (-(h / 4)) := hd₂prop δ hδ hδ₂
  have hlog := hd₁prop δ hδ hδ₁ n (n_bound hδ hδ1 hη1 hA)
  obtain ⟨hn, hi, -, hAmass, -, -⟩ := id hA
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρlow, hg, hbroad, hH, hterm⟩ := hD
  obtain ⟨hρup, hlen, hgζ⟩ := hterm rfl
  obtain ⟨hCZ, -, -, -, -, -, hCbal, -, -⟩ := id hC
  have hδρ : δ ≤ ρ := by
    calc δ = δ ^ (1:ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (1 - ω / 100) := rpow_mono' hδ hδ1 (by linarith)
      _ ≤ ρ := hρlow
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hρ1 : ρ ≤ 1 := hρup.trans (Real.rpow_le_one hδ.le hδ1 (by positivity))
  have hA' := Ap_mono hδ hδ1 hηηR hA
  have hC' := Cp_mono hδ hδ1 hηηR hC
  have hbroad' : Broad δ ρ (δ ^ (-ηR)) (ω * ζ / 100) n N v S Z f :=
    Broad_mono hδ hρpos hbroad (rpow_neg_mono hδ hδ1 hηηR)
  rcases hRp δ hδ hδR n x v Y hA' ρ S Z N y w f hC' hδρ hρ1 hbroad' with
    hgain | ⟨S', Z', hS'S, hZ', hmass, hB⟩
  · exact Or.inl hgain
  right
  obtain ⟨R, S₁, E, ℓ, hS₁, hmemR, hRS, hbal, hE, hmult, hsel⟩ :=
    select volume S' f Z' (fun i => (hZ' i).1)
  set Φ₂ := ∑ i ∈ S₁, volume (Z' i ∩ E (f i)) with hΦ₂def
  -- the retained mass
  have hmass2 : ENNReal.ofReal (δ ^ (h / 2)) * ∑ i, volume (Y i) ≤ Φ₂ := by
    have hL : (((Nat.log 2 n + 1) ^ 2 : ℕ) : ENNReal) =
        ENNReal.ofReal (((Nat.log 2 n : ℝ) + 1) ^ 2) := by
      rw [← ENNReal.ofReal_natCast]
      push_cast
      rfl
    have hprod : δ ^ (h / 4) * (((Nat.log 2 n : ℝ) + 1) ^ 2) ≤ 1 := by
      have e : δ ^ (h / 4) * δ ^ (-(h / 4)) = 1 := by
        rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
      have h0 : 0 ≤ δ ^ (h / 4) := Real.rpow_nonneg hδ.le _
      calc δ ^ (h / 4) * (((Nat.log 2 n : ℝ) + 1) ^ 2) ≤ δ ^ (h / 4) * δ ^ (-(h / 4)) :=
            mul_le_mul_of_nonneg_left hlog h0
        _ = 1 := e
    calc ENNReal.ofReal (δ ^ (h / 2)) * ∑ i, volume (Y i)
        = ENNReal.ofReal (δ ^ (h / 4)) * (ENNReal.ofReal (δ ^ (h / 4)) * ∑ i, volume (Y i)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
          congr 3; ring
      _ ≤ ENNReal.ofReal (δ ^ (h / 4)) * ((((Nat.log 2 n + 1) ^ 2 : ℕ) : ENNReal) * Φ₂) :=
          mul_le_mul' le_rfl (hmass.trans hsel)
      _ = ENNReal.ofReal (δ ^ (h / 4) * (((Nat.log 2 n : ℝ) + 1) ^ 2)) * Φ₂ := by
          rw [hL, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      _ ≤ ENNReal.ofReal 1 * Φ₂ := by gcongr
      _ = Φ₂ := by simp
  have hYpos : 0 < ∑ i, volume (Y i) := by
    refine lt_of_lt_of_le ?_ hAmass
    apply ENNReal.ofReal_pos.2
    have := Real.rpow_pos_of_pos hδ η
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hΦ₂ne : Φ₂ ≠ 0 := by
    intro h0
    rw [h0] at hmass2
    have h00 : ENNReal.ofReal (δ ^ (h / 2)) * ∑ i, volume (Y i) = 0 := le_antisymm hmass2 bot_le
    rcases mul_eq_zero.1 h00 with h1 | h1
    · have := ENNReal.ofReal_eq_zero.1 h1
      have := Real.rpow_pos_of_pos hδ (h / 2)
      linarith
    · exact hYpos.ne' h1
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_of_sum_ne_zero hΦ₂ne
  have hRne : 0 < R.card := card_pos.2 ⟨f i₀, (hmemR i₀ (hS₁ hi₀)).1 hi₀⟩
  set k0 : Fin R.card := ⟨0, hRne⟩ with hk0
  -- the number of retained coarse tubes
  have hvolT : ∀ i, volume (Tb δ (x i) (v i)) ≤ ENNReal.ofReal (56 * δ ^ 2) := fun i =>
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.tube_volume_upper hδ.le hδ1 (x i) (v i)
      ((hi i).1)
  have hΦ₂up : Φ₂ ≤ ENNReal.ofReal ((S₁.card : ℝ) * (56 * δ ^ 2)) := by
    calc Φ₂ ≤ ∑ i ∈ S₁, ENNReal.ofReal (56 * δ ^ 2) := by
          refine sum_le_sum (fun i _ => ?_)
          calc volume (Z' i ∩ E (f i)) ≤ volume (Y i) :=
                measure_mono (Set.inter_subset_left.trans ((hZ' i).2.1.trans (hCZ i).2.1))
            _ ≤ volume (Tb δ (x i) (v i)) := measure_mono (hi i).2.2.2
            _ ≤ _ := hvolT i
      _ = ENNReal.ofReal ((S₁.card : ℝ) * (56 * δ ^ 2)) := by
          rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hreal1 : δ ^ (h / 2) * (δ ^ η * n * δ ^ 2) ≤ (S₁.card : ℝ) * (56 * δ ^ 2) := by
    have : ENNReal.ofReal (δ ^ (h / 2) * (δ ^ η * n * δ ^ 2)) ≤
        ENNReal.ofReal ((S₁.card : ℝ) * (56 * δ ^ 2)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      calc ENNReal.ofReal (δ ^ (h / 2)) * ENNReal.ofReal (δ ^ η * n * δ ^ 2)
          ≤ ENNReal.ofReal (δ ^ (h / 2)) * ∑ i, volume (Y i) := by gcongr
        _ ≤ Φ₂ := hmass2
        _ ≤ _ := hΦ₂up
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hcard : (S₁.card : ℝ) * N ≤ R.card * (δ ^ (-η) * n) := by
    have hbalS : ∀ k k', (fc S f k : ℝ) ≤ δ ^ (-η) * fc S f k' := by
      intro k k'
      have := hCbal k k'
      rwa [qc_fibre, qc_fibre] at this
    have hsum : ∑ k' : Fin N, (fc S f k' : ℝ) = S.card := by
      have := card_eq_sum_card_fiberwise (f := f) (s := S) (t := univ)
        (fun i _ => mem_coe.2 (mem_univ _))
      unfold fc
      exact_mod_cast this.symm
    have hSn : (S.card : ℝ) ≤ n := by
      have := card_le_univ S
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hfibS : ∀ k, (N : ℝ) * fc S f k ≤ δ ^ (-η) * n := by
      intro k
      calc (N : ℝ) * fc S f k = ∑ _k' : Fin N, (fc S f k : ℝ) := by simp
        _ ≤ ∑ k' : Fin N, δ ^ (-η) * fc S f k' := sum_le_sum (fun k' _ => hbalS k k')
        _ = δ ^ (-η) * S.card := by rw [← mul_sum, hsum]
        _ ≤ δ ^ (-η) * n := mul_le_mul_of_nonneg_left hSn (Real.rpow_nonneg hδ.le _)
    have hS₁sum : (S₁.card : ℝ) = ∑ k ∈ R, ((S₁.filter (fun i => f i = k)).card : ℝ) := by
      have := card_eq_sum_card_fiberwise (f := f) (s := S₁) (t := R)
        (fun i hi => mem_coe.2 ((hmemR i (hS₁ (mem_coe.1 hi))).1 (mem_coe.1 hi)))
      exact_mod_cast this
    have hfibsub : ∀ k, ((S₁.filter (fun i => f i = k)).card : ℝ) ≤ fc S f k := by
      intro k
      unfold fc
      exact_mod_cast card_le_card (filter_subset_filter _ (hS₁.trans hS'S))
    calc (S₁.card : ℝ) * N = ∑ k ∈ R, ((S₁.filter (fun i => f i = k)).card : ℝ) * N := by
          rw [hS₁sum, sum_mul]
      _ ≤ ∑ k ∈ R, (N : ℝ) * fc S f k := by
          refine sum_le_sum (fun k _ => ?_)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hfibsub k) (Nat.cast_nonneg _)
      _ ≤ ∑ _k ∈ R, δ ^ (-η) * n := sum_le_sum (fun k _ => hfibS k)
      _ = R.card * (δ ^ (-η) * n) := by rw [sum_const, nsmul_eq_mul]
  have hbudget : δ ^ (-η) * N ≤ δ ^ (-h) * R.card :=
    budget_arith hδ hδ1 (by exact_mod_cast hn) (Nat.cast_nonneg _) hηh12 hηpos h56 hreal1 hcard
  -- the inputs of the grain restoration
  have hsh : 2 * δ ^ h ≤ δ ^ (h / 2) * δ ^ η := by
    have e1 : δ ^ h = (δ ^ (h / 2) * δ ^ η) * δ ^ (h / 2 - η) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
    have h1 : δ ^ (h / 2 - η) ≤ δ ^ (h / 4) := rpow_mono' hδ hδ1 (by linarith)
    have h2 : δ ^ (-(h / 4)) * δ ^ (h / 4) = 1 := by
      rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
    have h3 : 0 < δ ^ (h / 4) := Real.rpow_pos_of_pos hδ _
    have h4 : 0 < δ ^ (h / 2) * δ ^ η := by
      have := Real.rpow_pos_of_pos hδ (h / 2)
      have := Real.rpow_pos_of_pos hδ η
      positivity
    have h6 : 56 * δ ^ (h / 4) ≤ 1 := by
      calc 56 * δ ^ (h / 4) ≤ δ ^ (-(h / 4)) * δ ^ (h / 4) :=
            mul_le_mul_of_nonneg_right h56 h3.le
        _ = 1 := h2
    have h5 : 2 * δ ^ (h / 2 - η) ≤ 1 := by linarith
    rw [e1]
    calc 2 * ((δ ^ (h / 2) * δ ^ η) * δ ^ (h / 2 - η))
        = (δ ^ (h / 2) * δ ^ η) * (2 * δ ^ (h / 2 - η)) := by ring
      _ ≤ (δ ^ (h / 2) * δ ^ η) * 1 := mul_le_mul_of_nonneg_left h5 h4.le
      _ = δ ^ (h / 2) * δ ^ η := mul_one _
  have hΦ : ENNReal.ofReal (δ ^ (h / 2)) * ∑ i ∈ S, volume (Z i) ≤ Φ₂ := by
    refine le_trans ?_ hmass2
    refine mul_le_mul' le_rfl ?_
    calc ∑ i ∈ S, volume (Z i) ≤ ∑ i ∈ S, volume (Y i) :=
          sum_le_sum (fun i _ => measure_mono (hCZ i).2.1)
      _ ≤ ∑ i, volume (Y i) := sum_le_sum_of_subset (subset_univ _)
  have hmassh : ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ Φ₂ := by
    refine le_trans ?_ hmass2
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (rpow_mono' hδ hδ1 (by linarith))) le_rfl
  have h2 : (2:ℝ) ≤ δ ^ (-h) := by
    have : δ ^ (-(h / 4)) ≤ δ ^ (-h) := rpow_neg_mono hδ hδ1 (by linarith)
    linarith
  refine ⟨S₁, fun i => if i ∈ S₁ then Z' i ∩ E (f i) else ∅, ρ, R.card,
    fun k => y (emb R k), fun k => w (emb R k), fun i => back R k0 (f i), ?_⟩
  unfold Gp
  refine ⟨restore_cover hδ hδ1 (by linarith) (by linarith) h2 hC hS'S hZ' hB k0 hS₁ hmemR hbal
    hE hmassh hbudget, hρlow, hρup, a, c, ?_⟩
  exact restore_grains hδ hδ1 hn hρpos hζh (fun i => (hCZ i).1) hH hlen hgζ hS'S hZ' k0 hS₁
    hmemR hE hmult (Real.rpow_nonneg hδ.le _) hΦ hsh

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
