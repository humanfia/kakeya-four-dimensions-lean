-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Estimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_endpoint_bootstrap

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- Common hypotheses on a shaded, essentially distinct tube family. -/
def Admissible (δ η : ℝ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
    (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) ∧
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) ∧
    (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ tube δ (x i) (v i)) ∧ Dense δ η Y

/-- The coefficient of the restricted estimate, with its scale factor omitted. -/
noncomputable def restrictedCoefficient (σ δ m N : ℝ) : ℝ :=
  m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)

/-- The restricted estimate (the paper's tilde-E). -/
def Restricted (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η x v Y → Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

/-- The full E estimate, allowing arbitrary convex and slab constants. -/
def Full (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η x v Y → Katz δ m x v → Frostman δ l x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem Admissible.mono {δ η η' : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : Admissible δ η x v Y) : Admissible δ η' x v Y :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.mono hδ hδ1 hη⟩

theorem restrictedCoefficient_eq {σ δ m N : ℝ} (hm : 0 < m) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) :
    restrictedCoefficient σ δ m N =
      (N * δ ^ 2) * (N * δ) ^ (-σ) * m ^ (3 * σ / 2 - 1) := by
  unfold restrictedCoefficient
  rw [Real.mul_rpow (Real.rpow_nonneg hm.le _) (mul_nonneg hN hδ),
    ← Real.rpow_mul hm.le, show -(3 / 2 : ℝ) * -σ = 3 * σ / 2 by ring]
  rw [show m⁻¹ = m ^ (-1 : ℝ) by rw [Real.rpow_neg_one]]
  rw [show 3 * σ / 2 - 1 = -1 + 3 * σ / 2 by ring, Real.rpow_add hm]
  ring

theorem restrictedCoefficient_nonneg {σ δ m N : ℝ} (hm : 0 ≤ m) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ) : 0 ≤ restrictedCoefficient σ δ m N := by
  unfold restrictedCoefficient
  positivity

/-- In the range used here, increasing the convex error decreases the coefficient. -/
theorem restrictedCoefficient_antitone {σ δ m m' N : ℝ}
    (hσ : σ ≤ 2 / 3) (hm : 0 < m) (hmm : m ≤ m')
    (hN : 0 ≤ N) (hδ : 0 ≤ δ) :
    restrictedCoefficient σ δ m' N ≤ restrictedCoefficient σ δ m N := by
  rw [restrictedCoefficient_eq (hm.trans_le hmm) hN hδ,
    restrictedCoefficient_eq hm hN hδ]
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_nonpos hm hmm (by linarith)
  · positivity

/-- For a convex constant at least one, the restricted coefficient is bounded
by the D coefficient. -/
theorem restrictedCoefficient_le {σ δ m N : ℝ} (hσ : σ ≤ 2 / 3)
    (hm : 1 ≤ m) (hN : 0 ≤ N) (hδ : 0 ≤ δ) :
    restrictedCoefficient σ δ m N ≤ (N * δ ^ 2) * (N * δ) ^ (-σ) := by
  simpa [restrictedCoefficient] using
    restrictedCoefficient_antitone hσ zero_lt_one hm hN hδ

/-- Direct application of D when the convex error is within D's allowed range. -/
theorem small_katz_improvement {σ ω ω' α : ℝ}
    (hσ : σ ≤ 2 / 3) (hgap : ω ≤ ω' - α) (hD : Estimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
      ∀ m : ℝ, 1 ≤ m → m ≤ δ ^ (-η) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η x v Y → Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
      ENNReal.ofReal (a * δ ^ ((ω' - α) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hD ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m hm hmη n x v Y hA hK hF
  rcases hA with ⟨hn, hv, hb, hd, hmeas, hY, hden⟩
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h δ hδ hδ100 n x v Y hn hv hb hd
    hmeas hY hden (hK.mono hmη) hF)
  have hc := restrictedCoefficient_le hσ hm (Nat.cast_nonneg n) hδ.le
  have hp : δ ^ ((ω' - α) + ε) ≤ δ ^ (ω + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  calc
    _ = a * δ ^ ((ω' - α) + ε) * restrictedCoefficient σ δ m (n : ℝ) := by
      unfold restrictedCoefficient
      ring
    _ ≤ a * δ ^ (ω + ε) * (((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp ha.le) hc
        (restrictedCoefficient_nonneg (by linarith) (Nat.cast_nonneg n) hδ.le)
        (by positivity)
    _ = _ := by ring

/-- Restriction to a subpower slab error costs an arbitrarily small scale power. -/
theorem Full.restricted {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : Full σ ω) :
    Restricted σ ω := by
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, h⟩ := hE (ε / 2) (by positivity)
  let η := min η₀ (ε / (2 * (σ + 1)))
  have hη : 0 < η := lt_min hη₀ (div_pos hε (by positivity))
  have hησ : η * σ ≤ ε / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (σ + 1))).1
      (min_le_right η₀ (ε / (2 * (σ + 1))))
    change η * (2 * (σ + 1)) ≤ ε at hh
    nlinarith
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m hm n x v Y hA hK hF
  have hδ1 : δ ≤ 1 := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hNδ : 0 < (n : ℝ) * δ := mul_pos (Nat.cast_pos.2 hA.1) hδ
  have hl : 1 ≤ δ ^ (-η) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_nonpos.2 hη.le)
  have hold := h δ hδ hδ100 m (δ ^ (-η)) hm hl n x v Y
    (hA.mono hδ hδ1 (min_le_left _ _)) hK hF
  apply le_trans (ENNReal.ofReal_le_ofReal _) hold
  have heq : (m ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * ((n : ℝ) * δ)) ^ (-σ) =
      δ ^ (η * σ) * (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ) := by
    rw [show m ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * ((n : ℝ) * δ) =
      δ ^ (-η) * (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) by ring,
      Real.mul_rpow (Real.rpow_nonneg hδ.le _)
        (mul_nonneg (Real.rpow_nonneg hm0.le _) hNδ.le),
      ← Real.rpow_mul hδ.le]
    congr 2
    ring
  rw [heq]
  calc
    _ = a * δ ^ (ω + ε) * restrictedCoefficient σ δ m (n : ℝ) := by
      unfold restrictedCoefficient
      ring
    _ ≤ a * δ ^ ((ω + ε / 2) + η * σ) * restrictedCoefficient σ δ m (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) ha.le)
        (restrictedCoefficient_nonneg hm0.le (Nat.cast_nonneg n) hδ.le)
    _ = _ := by
      rw [Real.rpow_add hδ]
      unfold restrictedCoefficient
      ring

theorem Restricted.mono_omega {σ ω ω' : ℝ} (hω : ω ≤ ω')
    (hR : Restricted σ ω) : Restricted σ ω' := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hR ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m hm n x v Y hA hK hF
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h δ hδ hδ100 m hm n x v Y hA hK hF)
  have hp : δ ^ (ω' + ε) ≤ δ ^ (ω + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  gcongr

theorem Restricted.closed_omega {σ ω : ℝ}
    (hR : ∀ e > 0, Restricted σ (ω + e)) : Restricted σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hR (ε / 2) (by positivity) (ε / 2) (by positivity)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m hm n x v Y hA hK hF
  simpa only [show (ω + ε / 2) + ε / 2 = ω + ε by ring] using
    h δ hδ hδ100 m hm n x v Y hA hK hF

theorem Full.mono_omega {σ ω ω' : ℝ} (hω : ω ≤ ω')
    (hE : Full σ ω) : Full σ ω' := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hA hK hF
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h δ hδ hδ100 m l hm hl n x v Y hA hK hF)
  have hp : δ ^ (ω' + ε) ≤ δ ^ (ω + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  gcongr

theorem Full.closed_omega {σ ω : ℝ}
    (hE : ∀ e > 0, Full σ (ω + e)) : Full σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE (ε / 2) (by positivity) (ε / 2) (by positivity)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hA hK hF
  simpa only [show (ω + ε / 2) + ε / 2 = ω + ε by ring] using
    h δ hδ hδ100 m l hm hl n x v Y hA hK hF

end WangZahlLot.Obl.wz_restricted_uniform_improvement
