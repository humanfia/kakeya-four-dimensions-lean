import Submission.Obl.k4_finite_width_output_exclusion.Limits

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

abbrev Scenario (m : ℕ) := Option (Fin m × Bool)

def scenarioTime {m : ℕ} (s : ℕ → ℝ) (kr Δ e : ℝ) : Scenario m → ℝ
  | none => kr * Δ / 2
  | some (i, false) => kr * s i + e + kr * Δ / 2
  | some (i, true) => kr * s i + e

def scenarioWidth {m : ℕ} (s : ℕ → ℝ) (ell Δ zeta : ℝ) : Scenario m → ℝ
  | some (i, true) => ell * s i + Δ - 4 * zeta
  | _ => 0

def scenarioDepth {m : ℕ} (s : ℕ → ℝ) (Δ e : ℝ) (r : ℝ) : Scenario m → Prop
  | none => Δ ≤ r
  | some (i, false) => s i - e + Δ ≤ r
  | some (i, true) => |r - s i| ≤ e

def Sample (p : Data) (k M D : ℕ) (τ : ℝ) {m : ℕ} (s : ℕ → ℝ)
    (kr ell Δ zeta e : ℝ) (sc : Scenario m) : Prop :=
  ∃ (r : ℝ) (a : Atlas p k), 0 ≤ r ∧ r + Δ ≤ 1 ∧ scenarioDepth s Δ e r sc ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ scenarioTime s kr Δ e sc ∧
    (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤
      p.N k ^ (-scenarioWidth s ell Δ zeta sc + 2 * τ)) ∧
    a.KnownAt M D (p.N k ^ τ) r

def NoImprovement (p : Data) (kr ell Δ zeta e : ℝ) : Prop :=
  (∀ r h w : ℝ, 0 ≤ r → r + Δ ≤ 1 →
    h ≤ kr * r - kr * Δ / 2 + (kr + 1) * e → ¬ Known p r h w) ∧
  (∀ r s : ℝ, 0 ≤ r → r + Δ ≤ 1 → |r - s| ≤ e →
    ¬ Known p r (kr * s + e) (ell * s + Δ - 4 * zeta))

def PathBounds (p : Data) (k m : ℕ) (s : ℕ → ℝ) (kr ell zeta e : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) : Prop :=
  r (m - 1) = 1 ∧ ∀ i, i < m → |r i - s i| ≤ e ∧ 0 < r i ∧
    p.N k ^ (kr * s i - e) ≤ (2 : ℝ) ^ T i ∧
    (2 : ℝ) ^ T i ≤ p.N k ^ (kr * s i + e) ∧ |nw i - ell * s i| ≤ 4 * zeta

def Improved (p : Data) (k M D : ℕ) (τ Δ kr : ℝ) (m : ℕ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) : Prop :=
  ∃ (r₂ : ℝ) (a : Atlas p k), r₂ + Δ ≤ 1 ∧
    ((Δ ≤ r₂ ∧ (2 : ℝ) ^ a.T ≤ p.N k ^ (kr * Δ / 2)) ∨
      ∃ i, i < m ∧
        ((r i + Δ ≤ r₂ ∧ (2 : ℝ) ^ a.T ≤ (2 : ℝ) ^ T i * p.N k ^ (kr * Δ / 2)) ∨
          (r₂ = r i ∧ a.T = T i ∧
            ∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-(nw i + Δ))))) ∧
    a.KnownAt M D (p.N k ^ τ) r₂

lemma scenarioDepth_closed {m : ℕ} (s : ℕ → ℝ) (Δ e : ℝ) (sc : Scenario m) :
    IsClosed {r : ℝ | scenarioDepth s Δ e r sc} := by
  rcases sc with _ | ⟨i, b⟩
  · exact isClosed_Ici
  · cases b
    · exact isClosed_Ici
    · exact isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const

lemma not_known_scenario {p : Data} {kr ell Δ zeta e : ℝ}
    (hkr : 0 ≤ kr) (he : 0 ≤ e) (hn : NoImprovement p kr ell Δ zeta e)
    {m : ℕ} (s : ℕ → ℝ) (sc : Scenario m) {r : ℝ} (hr : 0 ≤ r)
    (hrΔ : r + Δ ≤ 1) (hsc : scenarioDepth s Δ e r sc) :
    ¬ Known p r (scenarioTime s kr Δ e sc) (scenarioWidth s ell Δ zeta sc) := by
  rcases sc with _ | ⟨i, b⟩
  · apply hn.1 r _ _ hr hrΔ
    change Δ ≤ r at hsc
    dsimp only [scenarioTime]
    nlinarith [mul_nonneg hkr (sub_nonneg.2 hsc)]
  · cases b
    · apply hn.1 r _ _ hr hrΔ
      change s i - e + Δ ≤ r at hsc
      dsimp only [scenarioTime]
      nlinarith [mul_nonneg hkr (sub_nonneg.2 hsc)]
    · exact hn.2 r (s i) hr hrΔ hsc

lemma improved_to_sample {p : Data} (hp : Valid p) (hpL : p.L = 1)
    {k M D m : ℕ} {τ Δ kr ell zeta e : ℝ} (hτ : 0 ≤ τ) (hΔ : 0 < Δ)
    {s r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    (hpath : PathBounds p k m s kr ell zeta e r T nw)
    (hout : Improved p k M D τ Δ kr m r T nw) :
    ∃ sc : Scenario m, Sample p k M D τ s kr ell Δ zeta e sc := by
  obtain ⟨r₂, a, hrΔ, hcases, ha⟩ := hout
  have hwide : ∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (2 * τ) := by
    intro b
    have hb := det_time_bound (Real.rpow_nonneg (hp.scale_pos k).le τ) (ha.1.2.2.1 b)
    have heq : (p.N k ^ τ) ^ 2 = p.N k ^ (2 * τ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hp.scale_pos k).le]
      congr 1
      ring
    exact hb.trans_eq heq
  rcases hcases with hinit | ⟨i, hi, htime | hwidth⟩
  · refine ⟨none, r₂, a, le_trans hΔ.le hinit.1, hrΔ, hinit.1, hinit.2, ?_, ha⟩
    simpa only [scenarioWidth, neg_zero, zero_add] using hwide
  · have hri := hpath.2 i hi
    refine ⟨some (⟨i, hi⟩, false), r₂, a, ?_, hrΔ, ?_, ?_, ?_, ha⟩
    · linarith [hri.2.1]
    · change s i - e + Δ ≤ r₂
      linarith [(abs_le.1 hri.1).1]
    · change (2 : ℝ) ^ a.T ≤ p.N k ^ (kr * s i + e + kr * Δ / 2)
      calc
        (2 : ℝ) ^ a.T ≤ (2 : ℝ) ^ T i * p.N k ^ (kr * Δ / 2) := htime.2
        _ ≤ p.N k ^ (kr * s i + e) * p.N k ^ (kr * Δ / 2) :=
          mul_le_mul_of_nonneg_right hri.2.2.2.1 (Real.rpow_pos_of_pos (hp.scale_pos k) _).le
        _ = p.N k ^ (kr * s i + e + kr * Δ / 2) := (Real.rpow_add (hp.scale_pos k) _ _).symm
    · simpa only [scenarioWidth, neg_zero, zero_add] using hwide
  · have hri := hpath.2 i hi
    refine ⟨some (⟨i, hi⟩, true), r₂, a, ?_, hrΔ, ?_, ?_, ?_, ha⟩
    · rw [hwidth.1]
      exact hri.2.1.le
    · change |r₂ - s i| ≤ e
      simpa only [hwidth.1] using hri.1
    · change (2 : ℝ) ^ a.T ≤ p.N k ^ (kr * s i + e)
      simpa only [hwidth.2.1] using hri.2.2.2.1
    · intro b
      apply (hwidth.2.2 b).trans
      apply Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k)
      change -(nw i + Δ) ≤ -(ell * s i + Δ - 4 * zeta) + 2 * τ
      linarith [(abs_le.1 hri.2.2.2.2).1]

end
end Submission.Obl.k4_finite_width_output_exclusion
