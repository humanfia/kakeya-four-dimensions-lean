-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SaturationBridge.lean
import Submission.Obl.k4_terminal_label_saturation.Saturation

/-!
# Saturation of one sample of the frozen true terminal system

`saturation_of_charts` takes the frozen single-chart predicate `chart` (with the
true floor as its extra condition) for every chart of one sample, together with
the density representation and the typical upper cap at the terminal depth, and
returns the saturated selections `satSel`, range-restricted lists `satListR`
of size at most `H`, knowledge of every retained incidence, the explicit mass
loss, measurability, and fixed polynomial format of both the selections and the
list-membership fibres.  The hidden-coordinate range is `[-2 Nk^M, 2 Nk^M]`.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- Saturation of one sample of a true terminal system, from the frozen chart
predicate. -/
theorem saturation_of_charts {W C' T M D : ℕ} (Nk L : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (g : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ≥0∞) {κ n₀ cap H : ℝ}
    (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hNk : 1 ≤ Nk) (hB : ∀ γ₁, 0 < B γ₁) (hκ : 1 ≤ κ) (hn₀ : 0 < n₀) (hcap : 0 ≤ cap)
    (hH : 0 < H) (hgm : ∀ γ₁, Measurable (g γ₁))
    (hmap : ∀ γ₁, Measure.map (obs (B γ₁) (δ Nk L)) (((ν γ₁).prod volume).restrict (E γ₁)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (g γ₁))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hchart : ∀ b, chart Nk M D κ T ((j b : ℕ) : ℝ) L (B (γ b)) (E (γ b)) (c b) (u b) (Q b)
      (R b) (A b) (F b)
      (ENNReal.ofReal (n₀ * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ b)).prod volume) (F b)))
    (θ : ℝ≥0∞)
    (htyp : ∑ γ₁, ENNReal.ofReal (ω γ₁) * (((ν γ₁).prod volume).restrict (E γ₁))
      {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) (δ Nk L) p)} ≤ θ) :
    -- knowledge through the range-restricted lists
    (∀ b, ∀ p ∈ satSel γ j κ (δ Nk L) B c u Q R H F b,
      b ∈ satListR γ j κ (δ Nk L) B c u Q R H (2 * Nk ^ M) (γ b) (obs (B (γ b)) (δ Nk L) p)) ∧
    -- list sizes
    (∀ γ₁ o, ((satListR γ j κ (δ Nk L) B c u Q R H (2 * Nk ^ M) γ₁ o).card : ℝ) ≤ H) ∧
    -- retained selections
    (∀ b, satSel γ j κ (δ Nk L) B c u Q R H F b ⊆ F b) ∧
    (∀ b, MeasurableSet (satSel γ j κ (δ Nk L) B c u Q R H F b)) ∧
    -- mass
    ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) ≤
      ∑ b, ENNReal.ofReal (ω (γ b)) *
          ((ν (γ b)).prod volume) (satSel γ j κ (δ Nk L) B c u Q R H F b) +
        2 * θ + 2 * ENNReal.ofReal (cap * (Real.pi * κ ^ 3 * (14 + 48 * κ ^ 2)) / (n₀ * H)) *
          ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) ∧
    -- formats
    (∀ b (i : ℕ), fmt 7 (Nk ^ M + (2 + ((binCount (2 * Nk ^ M) (B (γ b)) (δ Nk L) + 1) +
        binCount (2 * Nk ^ M) (B (γ b)) (δ Nk L) * (C' * 6)))) (max D 4)
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈
        satSel γ j κ (δ Nk L) B c u Q R H F b}) ∧
    (∀ γ₁ b₀ (i : ℕ), fmt 7 ((binCount (2 * Nk ^ M) (B γ₁) (δ Nk L) + 1) +
        binCount (2 * Nk ^ M) (B γ₁) (δ Nk L) * (C' * 6)) 4
      {z : Fin 7 → ℝ | b₀ ∈ satListR γ j κ (δ Nk L) B c u Q R H (2 * Nk ^ M) γ₁
        (obs (B γ₁) (δ Nk L) ((i, fun e : Fin 6 => z e.castSucc), z 6))}) ∧
    (∀ γ₁ b₀, MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × ℝ |
      b₀ ∈ satListR γ j κ (δ Nk L) B c u Q R H (2 * Nk ^ M) γ₁ (obs (B γ₁) (δ Nk L) p)}) := by
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  have hκ0 : (0 : ℝ) ≤ κ := le_trans zero_le_one hκ
  have hNM : (0 : ℝ) ≤ Nk ^ M := by positivity
  -- unpack the chart predicate
  have hQ : ∀ b, (Q b).det ≠ 0 := fun b => (hchart b).1
  have hR : ∀ b, (R b).totalDegree ≤ 2 := fun b => (hchart b).2.2.2.2.1
  have hFm : ∀ b, MeasurableSet (F b) := fun b => (hchart b).2.2.2.2.2.2.2.1
  have hFfmt : ∀ b (i : ℕ), fmt 7 (Nk ^ M) D
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ F b} :=
    fun b i => ((hchart b).2.2.2.2.2.2.2.2.1 i).2
  have hAc : ∀ b, ∀ l ∈ A b, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧
      ∀ t ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • u b)‖ ≤ κ ∧
        |eval (x l t) (R b)| ≤ κ * δ Nk L ∧
        |eval (x l t) (pderiv 3 (R b))| ≤ κ * B (γ b) ∧
        |eval (x l t) (pderiv 3 (pderiv 3 (R b)))| ≤ κ * B (γ b) ^ 2 / δ Nk L :=
    fun b => (hchart b).2.2.2.2.2.2.2.2.2.1
  have hFc : ∀ b, ∀ p ∈ F b, p ∈ E (γ b) ∧ p.1 ∈ A b ∧
      p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧
      B (γ b) / κ ≤ |eval (x p.1 p.2) (pderiv 3 (R b))| :=
    fun b => (hchart b).2.2.2.2.2.2.2.2.2.2.1
  have hfloor : ∀ b, ENNReal.ofReal (n₀ * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν (γ b)).prod volume) (F b) := fun b => (hchart b).2.2.2.2.2.2.2.2.2.2.2
  have hA : ∀ b, ∀ l ∈ A b, ∀ t ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
        ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T),
      ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • u b)‖ ≤ κ ∧
      |eval (x l t) (R b)| ≤ κ * δ Nk L ∧
      |eval (x l t) (pderiv 3 (R b))| ≤ κ * B (γ b) ∧
      |eval (x l t) (pderiv 3 (pderiv 3 (R b)))| ≤ κ * B (γ b) ^ 2 / δ Nk L :=
    fun b l hl => (hAc b l hl).2.2
  -- the hidden coordinate of a selected incidence is at most `2 Nk^M`
  have hbound : ∀ b, ∀ p ∈ F b, |(x p.1 p.2) 3| ≤ 2 * Nk ^ M := by
    intro b p hp
    obtain ⟨_, hpA, hpt, _⟩ := hFc b p hp
    obtain ⟨_, hcoef, _⟩ := hAc b p.1 hpA
    have ht0 : 0 ≤ p.2 := by
      have := hpt.1
      have h0 : 0 ≤ ((j b : ℕ) : ℝ) / (2 : ℝ) ^ T := by positivity
      linarith
    have ht1 : p.2 ≤ 1 := by
      have := hpt.2
      have hj : ((j b : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
        have := (j b).isLt
        exact_mod_cast this
      have h1 : ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact hj
      linarith
    have hx : (x p.1 p.2) 3 = p.1.2 2 + p.2 * p.1.2 5 := rfl
    rw [hx]
    calc |p.1.2 2 + p.2 * p.1.2 5| ≤ |p.1.2 2| + |p.2 * p.1.2 5| := abs_add_le _ _
      _ = |p.1.2 2| + |p.2| * |p.1.2 5| := by rw [abs_mul]
      _ ≤ Nk ^ M + 1 * Nk ^ M := by
          gcongr
          · exact hcoef 2
          · rw [abs_of_nonneg ht0]; exact ht1
          · exact hcoef 5
      _ = 2 * Nk ^ M := by ring
  obtain ⟨hknow0, hmass⟩ := saturation_sample ω ν E B g γ j c u Q R A F hB hδ hκ hn₀ hcap hH hgm
    hmap hdisj hQ hR hFm hA hFc hfloor θ htyp
  refine ⟨?_, fun γ₁ o => satListR_card_le γ j κ (δ Nk L) B c u Q R hH.le _ γ₁ o,
    fun b => inter_subset_left, ?_, hmass, ?_, ?_, ?_⟩
  · intro b p hp
    have hp' := hknow0 b p hp
    -- membership in the unrestricted list gives chart compatibility
    have hmem : obs (B (γ b)) (δ Nk L) p ∈
        chartCompat T ((j b : ℕ) : ℝ) κ (δ Nk L) (B (γ b)) (c b) (u b) (Q b) (R b) := by
      obtain ⟨hpF, _⟩ := hp
      obtain ⟨_, hpA, hpt, hpfl⟩ := hFc b p hpF
      obtain ⟨hbox, hval, hder, hcurv⟩ := hA b p.1 hpA p.2 hpt
      exact obs_mem_chartCompat T ((j b : ℕ) : ℝ) hκ hδ (hB (γ b)) (c b) (u b) (Q b) (R b)
        (hR b) p hpt hbox hval hder hcurv hpfl
    exact mem_satListR_of_satSel γ j B c u Q R H F (by positivity) hδ hB b p hp hmem
      (hbound b p hp.1)
  · intro b
    have hGm := (measurable_obs (B (γ b)) (δ Nk L))
      (measurableSet_compatCharts_le γ j κ (δ Nk L) B c u Q R (γ b) hH.le)
    exact (hFm b).inter hGm
  · intro b i
    exact satSel_fmt γ j B c u Q R H F hκ0 hδ hB hR (by positivity) b (hbound b) i (hFfmt b i)
  · intro γ₁ b₀ i
    exact fmt_mem_satListR γ j B c u Q R H (2 * Nk ^ M) hκ0 hδ hB hR γ₁ b₀ i
  · intro γ₁ b₀
    exact measurableSet_mem_satListR γ j κ (δ Nk L) B c u Q R hH.le _ γ₁ b₀

end Submission.Obl.k4_terminal_label_saturation
