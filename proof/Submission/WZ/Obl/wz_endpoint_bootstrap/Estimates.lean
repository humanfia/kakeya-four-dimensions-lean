-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_endpoint_bootstrap.Estimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_endpoint_bootstrap

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

abbrev tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

def Katz (δ m : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (({i : Fin n | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal m * volume W

def Frostman (δ l : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i : Fin n | tube δ (x i) (v i) ⊆
      (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r})}.ncard : ℝ) ≤
    ENNReal.ofReal (l * (n : ℝ)) *
      volume (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r})

def Dense (δ η : ℝ) {n : ℕ} (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The normalized estimate denoted by D in the frozen statement. -/
def Estimate (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    0 < n → (∀ i, ‖v i‖ = 1) →
    (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    Dense δ η Y → Katz δ (δ ^ (-η)) x v → Frostman δ (δ ^ (-η)) x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * ((n : ℝ) * δ ^ 2) *
      ((n : ℝ) * δ) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem Katz.mono {δ m m' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hm : m ≤ m') (h : Katz δ m x v) : Katz δ m' x v := by
  intro W hW
  apply (h W hW).trans
  gcongr

theorem Frostman.mono {δ l l' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hl : l ≤ l') (h : Frostman δ l x v) : Frostman δ l' x v := by
  intro u t r hu hr
  apply (h u t r hu hr).trans
  gcongr

theorem Dense.mono {δ η η' : ℝ} {n : ℕ} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') (h : Dense δ η Y) :
    Dense δ η' Y := by
  apply le_trans (ENNReal.ofReal_le_ofReal _) h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη) (Nat.cast_nonneg n)) (sq_nonneg δ)

/-- A fixed finite upper bound for the volume of the containing ball. -/
noncomputable def ballConstant : ℝ := max 1 (volume (Metric.ball (0 : Space) 1)).toReal

theorem ballConstant_pos : 0 < ballConstant :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- The convex-count assumption alone gives all cardinality control needed
for the endpoint argument. -/
theorem Katz.card_bound {δ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ 1)
    (hb : ∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1)
    (hK : Katz δ (δ ^ (-η)) x v) :
    (n : ℝ) * δ ≤ ballConstant * δ ^ (-2 : ℝ) := by
  have hcount := hK (Metric.ball (0 : Space) 1) (convex_ball _ _)
  have hset : {i : Fin n | tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1} = Set.univ :=
    Set.eq_univ_of_forall hb
  rw [hset] at hcount
  simp only [Set.ncard_univ, Nat.card_fin] at hcount
  have hreal : (n : ℝ) * δ ^ 2 ≤
      δ ^ (-η) * (volume (Metric.ball (0 : Space) 1)).toReal := by
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) hcount
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (n : ℝ) * δ ^ 2),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _)] using ht
  have hpow : δ ^ (-η) ≤ δ ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hbound : (n : ℝ) * δ ^ 2 ≤ ballConstant * δ ^ (-1 : ℝ) := by
    calc
      _ ≤ δ ^ (-η) * (volume (Metric.ball (0 : Space) 1)).toReal := hreal
      _ ≤ δ ^ (-1 : ℝ) * ballConstant := mul_le_mul hpow
        (le_max_right _ _) ENNReal.toReal_nonneg (Real.rpow_nonneg hδ.le _)
      _ = _ := mul_comm _ _
  have hbound' : ((n : ℝ) * δ) * δ ^ 2 ≤ ballConstant := by
    calc
      _ = ((n : ℝ) * δ ^ 2) * δ := by ring
      _ ≤ (ballConstant * δ ^ (-1 : ℝ)) * δ :=
        mul_le_mul_of_nonneg_right hbound hδ.le
      _ = ballConstant := by rw [Real.rpow_neg_one]; field_simp
  rw [Real.rpow_neg hδ.le, Real.rpow_two, ← div_eq_mul_inv]
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).2 hbound'

/-- A change of cardinality exponent can be paid for by twice that change
in the scale exponent. -/
theorem exponent_bound {δ C N a B s t w ε : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hN : 0 < N) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hts : t ≤ s) (hbound : N ≤ C * δ ^ (-2 : ℝ)) :
    (a / C ^ (s - t)) * δ ^ ((w + 2 * (s - t)) + ε) * B * N ^ (-t) ≤
      a * δ ^ (w + ε) * B * N ^ (-s) := by
  have hp : N ^ (s - t) ≤ C ^ (s - t) * δ ^ (-2 * (s - t)) := by
    calc
      _ ≤ (C * δ ^ (-2 : ℝ)) ^ (s - t) :=
        Real.rpow_le_rpow hN.le hbound (sub_nonneg.2 hts)
      _ = _ := by rw [Real.mul_rpow hC.le (Real.rpow_nonneg hδ.le _),
        ← Real.rpow_mul hδ.le]
  have hcancel : δ ^ (2 * (s - t)) * δ ^ (-2 * (s - t)) = 1 := by
    rw [← Real.rpow_add hδ]
    rw [show 2 * (s - t) + -2 * (s - t) = 0 by ring, Real.rpow_zero]
  have haux : δ ^ (2 * (s - t)) * N ^ (s - t) ≤ C ^ (s - t) := by
    calc
      _ ≤ δ ^ (2 * (s - t)) * (C ^ (s - t) * δ ^ (-2 * (s - t))) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hδ.le _)
      _ = C ^ (s - t) * (δ ^ (2 * (s - t)) * δ ^ (-2 * (s - t))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have hfactor : (δ ^ (2 * (s - t)) * N ^ (s - t)) / C ^ (s - t) ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hC _)).2 haux
  calc
    _ = (a * δ ^ (w + ε) * B * N ^ (-s)) *
        ((δ ^ (2 * (s - t)) * N ^ (s - t)) / C ^ (s - t)) := by
      rw [show (w + 2 * (s - t)) + ε = (w + ε) + 2 * (s - t) by ring,
        Real.rpow_add hδ]
      conv_lhs => rw [show -t = -s + (s - t) by ring, Real.rpow_add hN]
      ring
    _ ≤ (a * δ ^ (w + ε) * B * N ^ (-s)) * 1 :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := mul_one _

theorem Estimate.mono_omega {s w w' : ℝ} (hww : w ≤ w')
    (hD : Estimate s w) : Estimate s w' := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hD ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hn hv hb hd hm hY hden hK hF
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h δ hδ hδ100 n x v Y hn hv hb hd hm hY hden hK hF)
  have hpow : δ ^ (w' + ε) ≤ δ ^ (w + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  gcongr

theorem Estimate.closed_omega {s w : ℝ}
    (hD : ∀ e > 0, Estimate s (w + e)) : Estimate s w := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hD (ε / 2) (by linarith) (ε / 2) (by linarith)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hn hv hb hd hm hY hden hK hF
  have heq : (w + ε / 2) + ε / 2 = w + ε := by ring
  simpa only [heq] using h δ hδ hδ100 n x v Y hn hv hb hd hm hY hden hK hF

theorem Estimate.shift {s t w : ℝ} (hts : t ≤ s)
    (hD : Estimate s w) : Estimate t (w + 2 * (s - t)) := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hD ε hε
  refine ⟨a / ballConstant ^ (s - t), div_pos ha (Real.rpow_pos_of_pos ballConstant_pos _),
    min η 1, lt_min hη zero_lt_one, ?_⟩
  intro δ hδ hδ100 n x v Y hn hv hb hd hm hY hden hK hF
  have hδ1 : δ ≤ 1 := by linarith
  have heta : δ ^ (-(min η 1)) ≤ δ ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_left _ _))
  have hold := h δ hδ hδ100 n x v Y hn hv hb hd hm hY
    (hden.mono hδ hδ1 (min_le_left _ _)) (hK.mono heta) (hF.mono heta)
  apply le_trans (ENNReal.ofReal_le_ofReal _) hold
  exact exponent_bound hδ ballConstant_pos (mul_pos (Nat.cast_pos.2 hn) hδ)
    ha.le (by positivity) hts (hK.card_bound hδ hδ1 (min_le_right _ _) hb)

end WangZahlLot.Obl.wz_endpoint_bootstrap
