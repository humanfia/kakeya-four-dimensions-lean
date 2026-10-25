import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_level_finite_gain.Numerics
import Submission.Obl.k4_oss_level_finite_gain.Reflection
import Submission.Obl.k4_oss_level_finite_gain.Frostman
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_level_finite_gain`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_level_finite_gain`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_level_finite_gain/`
belong to this obligation.
-/

open Submission.Obl.k4_oss_level_finite_gain

theorem Submission.k4_oss_level_finite_gain : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ θ rG : ℝ, 0 < θ → 0 < rG → rG ≤ 1 → (∀ δ : ℝ, 0 < δ → δ < rG → ∀ d : ℝ, 0 ≤ d → d ≤ 1 - (γ / 4) → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → (∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y) → (∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y) → (∀ x u : ℝ, δ ≤ u → ((A.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * (A.card : ℝ)) → (∀ x u : ℝ, δ ≤ u → ((B.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * (B.card : ℝ)) → δ ^ (θ - d) ≤ (A.card : ℝ) → (A.card : ℝ) ≤ δ ^ (-d - θ) → δ ^ (θ - d) ≤ (B.card : ℝ) → (B.card : ℝ) ≤ δ ^ (-d - θ) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2))) → MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤ ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))) → ∀ a : ℝ, 0 < a → 8 * a < θ → ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ r ≤ 1 ∧ r ≤ rG ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ (F : Finset ℝ) (p : ℝ → ℝ) (Z : ℝ), 0 ≤ Z → (∀ x ∈ F, 0 ≤ p x) → (∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y) → (∀ x u : ℝ, δ ≤ u → u ≤ (1 / 2 : ℝ) → ENNReal.ofReal (Finset.sum (F.filter (fun y => dist y x ≤ u)) p) ≤ ENNReal.ofReal (δ ^ (-ε) * (2 * u) ^ s)) → ∀ A C : Finset ℝ, A ⊆ F → C ⊆ F → A.Nonempty → C.Nonempty → ∀ q1 q2 : ℝ, 0 < q1 → 0 < q2 → (∀ x ∈ A, q1 ≤ p x) → (∀ x ∈ C, q2 ≤ p x) → (q1 * (A.card : ℝ) ≤ 1 ∧ q2 * (C.card : ℝ) ≤ 1 ∧ q1 ^ 2 * (A.card : ℝ) ≤ Z ∧ q2 ^ 2 * (C.card : ℝ) ≤ Z) → (δ ^ (2 * a) ≤ q1 * (A.card : ℝ) ∧ δ ^ (2 * a) ≤ q2 * (C.card : ℝ) ∧ (A.card : ℝ) ≤ δ ^ (-1 + γ / 2) ∧ (C.card : ℝ) ≤ δ ^ (-1 + γ / 2) ∧ (A.card : ℝ) ≤ δ ^ (-3 * a) * (C.card : ℝ) ∧ (C.card : ℝ) ≤ δ ^ (-3 * a) * (A.card : ℝ)) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-ε) * u ^ s)) → ENNReal.ofReal (q1 ^ 2 * q2 ^ 2) * (MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product C).product (A.product C)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 16 * δ)).card : ℝ)))) ≤ ENNReal.ofReal (δ ^ (2 * a) * Z) := by
  classical
  intro s hs hs1 γ hγ hγ1 θ rG hθ hrG hrG1 hgain a ha haθ
  obtain ⟨r₀, hr₀, hr₀1, habsorb⟩ :=
    Submission.Obl.k4_oss_unit_decay.small_absorb 4 (3 * a) θ (by linarith)
  refine ⟨a, min r₀ rG, ha, lt_min hr₀ hrG,
    (min_le_left _ _).trans hr₀1, min_le_right _ _, ?_⟩
  intro δ hδ hδr F p Z hZ hp hsep hcap A C hAF hCF hA hC
    q₁ q₂ hq₁ hq₂ hAp hCp hmass hbounds ν hν hνsupp hνcap
  have hδr₀ : δ < r₀ := hδr.trans_le (min_le_left _ _)
  have hδG : δ < rG := hδr.trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := hδr₀.trans_le hr₀1
  have hab : 4 * δ ^ (-3 * a) ≤ δ ^ (-θ) := by
    simpa only [neg_mul] using habsorb δ hδ hδr₀
  obtain ⟨hm₁, hm₂, hq₁Z, hq₂Z⟩ := hmass
  obtain ⟨hheavyA, hheavyC, hAcap, hCcap, hAC, hCA⟩ := hbounds
  let B := C.image (fun c => -2 * c)
  have hBC : B.card = C.card := Finset.card_image_of_injective C reflection_injective
  have hB : B.Nonempty := hC.image _
  have hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y :=
    fun x hx y hy hxy => hsep x (hAF hx) y (hAF hy) hxy
  have hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y :=
    reflected_separated hδ.le C (fun x hx y hy hxy => hsep x (hCF hx) y (hCF hy) hxy)
  have hAfrost := heavy_level_frostman hδ hδ1.le ha.le hs.le hs1 hab
    F A p q₁ hAF hp hAp hheavyA hcap
  have hCfrost := heavy_level_frostman hδ hδ1.le ha.le hs.le hs1 hab
    F C p q₂ hCF hp hCp hheavyC hcap
  have hBfrost : ∀ x u : ℝ, δ ≤ u →
      ((B.filter (fun b => dist b x ≤ u)).card : ℝ) ≤
        δ ^ (-θ) * u ^ (s / 2) * (B.card : ℝ) := by
    intro x u hδu
    calc
      _ ≤ ((C.filter (fun c => dist c (-x / 2) ≤ u)).card : ℝ) := by
        dsimp only [B]
        exact_mod_cast reflected_filter_card_le C x u (hδ.trans_le hδu).le
      _ ≤ δ ^ (-θ) * u ^ (s / 2) * (C.card : ℝ) := hCfrost (-x / 2) u hδu
      _ = _ := by rw [hBC]
  have hA1 : 1 ≤ (A.card : ℝ) := by
    have hh : 1 ≤ A.card := by have := hA.card_pos; omega
    exact_mod_cast hh
  have hAcap' : (A.card : ℝ) ≤ δ ^ (-(1 - γ / 2)) := by
    convert hAcap using 1
    congr 1
    ring
  obtain ⟨d, hd0, hdCap, hdBase⟩ := exists_card_dimension hδ hδ1 hA1 hAcap'
  have hdle : d ≤ 1 - γ / 4 := by linarith
  obtain ⟨hAlow, hAhigh⟩ := size_window (η := 0) (θ := θ) (M := (A.card : ℝ))
    hδ hδ1.le hθ.le
    (Nat.cast_nonneg _) hdBase (by simp) (by simp)
  obtain ⟨hClow, hChigh⟩ := size_window (η := 3 * a) (θ := θ) (M := (C.card : ℝ))
    hδ hδ1.le (by linarith)
    (Nat.cast_nonneg _) hdBase (by simpa only [neg_mul] using hAC)
      (by simpa only [neg_mul] using hCA)
  have hνweak : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2)) := by
    intro x u hδu hu1
    exact (hνcap x u hδu hu1).trans (ENNReal.ofReal_le_ofReal
      (direction_power_bound hδ hδ1.le ha.le hs.le (hδ.trans_le hδu) hu1 hab))
  have hE := hgain δ hδ hδG d hd0 hdle A B hA hB hAsep hBsep hAfrost hBfrost
    hAlow hAhigh (by rw [hBC]; exact hClow) (by rw [hBC]; exact hChigh)
      ν hν hνsupp hνweak
  simp only [B, reflected_energy_card,
    Finset.card_image_of_injective C reflection_injective] at hE
  calc
    _ ≤ ENNReal.ofReal (q₁ ^ 2 * q₂ ^ 2) *
        ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (C.card : ℝ)) :=
      by gcongr
    _ = ENNReal.ofReal ((q₁ ^ 2 * q₂ ^ 2) *
        (δ ^ θ * (A.card : ℝ) ^ 2 * (C.card : ℝ))) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ ^ (2 * a) * Z) :=
      ENNReal.ofReal_le_ofReal (weighted_gain_bound hδ hδ1.le (by linarith)
        hZ hq₁.le (Nat.cast_nonneg _) hm₁ hq₂Z)
