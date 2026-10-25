-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/RepresentativeBins.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0581 (with x0598), commit 583cb89a,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RepresentativeBins.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Directional
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RepresentativeSelection
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.JetLabels
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PacketRootTransfer

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MvPolynomial Submission.Lib.K4QuadraticSheets

/-- Absolute derivative windows with a common nonzero sign are the signed windows
used by the finite geometric tests. -/
theorem signed_window_of_abs {g σ : ℝ}
    (hlo : 19 / 20 * |σ| ≤ |g|) (hhi : |g| ≤ 21 / 20 * |σ|) (hsign : 0 < g * σ) :
    if decide (0 ≤ σ) then 19 / 20 * |σ| ≤ g ∧ g ≤ 21 / 20 * |σ|
    else 19 / 20 * |σ| ≤ -g ∧ -g ≤ 21 / 20 * |σ| := by
  rcases mul_pos_iff.mp hsign with ⟨hg, hσ⟩ | ⟨hg, hσ⟩
  · simpa only [abs_of_pos hg, show decide (0 ≤ σ) = true from decide_eq_true hσ.le,
      Bool.coe_true, ite_true] using And.intro hlo hhi
  · simpa only [abs_of_neg hg, show decide (0 ≤ σ) = false from decide_eq_false (not_le.mpr hσ),
      Bool.coe_false, ite_false] using And.intro hlo hhi

/-- Global bin-to-representative sheet control gives one geometric polynomial test
and scale for each merged bin, valid on every original member line of that bin. -/
theorem exists_bin_root_tests_bounded {n D : ℕ} {ι : Type*} [Fintype ι]
    (F : Fin n → RealSheet D) (jet : Fin n → ι → ℝ) (width : ι → ℝ)
    (P : Fin n → MvPolynomial (Fin 4) ℝ) (s : Fin n → ℝ) (pos : Fin n → Bool)
    (hP : ∀ a, (P a).totalDegree ≤ 2) (hs : ∀ a, 0 < s a)
    (A : Fin n → Set (ℕ × (Fin 6 → ℝ))) (base : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (B ηown ηbin ta tb : ℝ) (hB : 0 < B) (hηown : 0 < ηown) (hηbin : 0 ≤ ηbin)
    (hsource : ∀ a l, l ∈ A a → ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖base l t‖ ≤ (1 : ℝ) / 2 ∧
      |B * (Submission.Lib.K4XInterface.gx l t) 3 - ((F a).f (emb (base l t))).re| ≤ ηown)
    (hrepresentative : ∀ a x, ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖(F a).f (emb x) -
        (F (binRepresentative width jet (mergedLabel width jet a))).f (emb x)‖ ≤ ηbin)
    (hroots : ∀ a l t, ‖base l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F a).f (emb (base l t))).re / B
      eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (P a) = 0 ∧
      if pos a then
        19 / 20 * s a ≤ eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ∧
        eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ≤ 21 / 20 * s a
      else
        19 / 20 * s a ≤ -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ∧
        -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ≤ 21 / 20 * s a) :
    ∃ (Q : binLabels width jet → MvPolynomial (Fin 4) ℝ) (sq m₀ : binLabels width jet → ℝ),
      (∀ b, Q b = P (binRepresentative width jet b) ∨
        Q b = pderiv 3 (P (binRepresentative width jet b))) ∧
      (∀ b, sq b = s (binRepresentative width jet b) ∨
        sq b = |qc (P (binRepresentative width jet b))|) ∧
      (∀ b, (Q b).totalDegree ≤ 2 ∧ 0 < sq b ∧ 0 ≤ m₀ b ∧
        m₀ b ≤ 85 * sq b * ((ηown + ηbin) / B) ∧ |qc (Q b)| * m₀ b ≤ (sq b) ^ 2 / 40 ∧
        s (binRepresentative width jet b) / (1 + 80 * ((ηown + ηbin) / B)) ≤ sq b) ∧
      ∀ a l, l ∈ A a → l ∈ rootTestSet (Q (mergedLabel width jet a))
        (sq (mergedLabel width jet a)) (m₀ (mergedLabel width jet a)) ta tb := by
  classical
  let S (b : binLabels width jet) : Set (ℕ × (Fin 6 → ℝ)) :=
    {l | ∃ a, mergedLabel width jet a = b ∧ l ∈ A a}
  have hη : 0 < (ηown + ηbin) / B := div_pos (add_pos_of_pos_of_nonneg hηown hηbin) hB
  have hfits (b : binLabels width jet) : ∀ l ∈ S b, ∀ t,
      t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ∃ w : ℝ, eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ)
          (P (binRepresentative width jet b)) = 0 ∧
        |(Submission.Lib.K4XInterface.gx l t) 3 - w| ≤ (ηown + ηbin) / B ∧
        if pos (binRepresentative width jet b) then
          19 / 20 * s (binRepresentative width jet b) ≤
            eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ)
              (pderiv 3 (P (binRepresentative width jet b))) ∧
          eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ)
              (pderiv 3 (P (binRepresentative width jet b))) ≤ 21 / 20 * s (binRepresentative width jet b)
        else
          19 / 20 * s (binRepresentative width jet b) ≤
            -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ)
              (pderiv 3 (P (binRepresentative width jet b))) ∧
          -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ)
              (pderiv 3 (P (binRepresentative width jet b))) ≤ 21 / 20 * s (binRepresentative width jet b) := by
    intro l hl t ht
    obtain ⟨a, ha, hl⟩ := hl
    obtain ⟨hbase, hown⟩ := hsource a l hl t ht
    let rep := binRepresentative width jet b
    have hrep : ‖(F a).f (emb (base l t)) - (F rep).f (emb (base l t))‖ ≤ ηbin := by
      simpa only [ha] using hrepresentative a (base l t) hbase
    have hre : |((F a).f (emb (base l t))).re - ((F rep).f (emb (base l t))).re| ≤ ηbin := by
      have hh : |((F a).f (emb (base l t))).re - ((F rep).f (emb (base l t))).re| ≤
          ‖(F a).f (emb (base l t)) - (F rep).f (emb (base l t))‖ := by
        simpa only [Complex.sub_re] using
          Complex.abs_re_le_norm ((F a).f (emb (base l t)) - (F rep).f (emb (base l t)))
      exact hh.trans hrep
    have hfit : |B * (Submission.Lib.K4XInterface.gx l t) 3 -
        ((F rep).f (emb (base l t))).re| ≤ ηown + ηbin :=
      (abs_sub_le _ _ _).trans (add_le_add hown hre)
    obtain ⟨hroot, hwindow⟩ := hroots rep l t hbase
    exact ⟨((F rep).f (emb (base l t))).re / B, hroot,
      packet_hidden_fit_transfer hB hfit, hwindow⟩
  have hchoose (b : binLabels width jet) := representative_root_test_selection_bounded
    (hP (binRepresentative width jet b)) (hs (binRepresentative width jet b)) hη
    (pos (binRepresentative width jet b)) (S b) (hfits b)
  choose Q sq m₀ hQ hschoice hdegree hsq hm₀ hbound hcurv hlower hmembership using hchoose
  refine ⟨Q, sq, m₀, hQ, hschoice, fun b => ⟨hdegree b, hsq b, hm₀ b, hbound b, hcurv b, hlower b⟩, ?_⟩
  intro a l hl
  exact hmembership _ l ⟨a, rfl, hl⟩

theorem exists_bin_root_tests {n D : ℕ} {ι : Type*} [Fintype ι]
    (F : Fin n → RealSheet D) (jet : Fin n → ι → ℝ) (width : ι → ℝ)
    (P : Fin n → MvPolynomial (Fin 4) ℝ) (s : Fin n → ℝ) (pos : Fin n → Bool)
    (hP : ∀ a, (P a).totalDegree ≤ 2) (hs : ∀ a, 0 < s a)
    (A : Fin n → Set (ℕ × (Fin 6 → ℝ))) (base : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (B ηown ηbin ta tb : ℝ) (hB : 0 < B) (hηown : 0 < ηown) (hηbin : 0 ≤ ηbin)
    (hsource : ∀ a l, l ∈ A a → ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖base l t‖ ≤ (1 : ℝ) / 2 ∧
      |B * (Submission.Lib.K4XInterface.gx l t) 3 - ((F a).f (emb (base l t))).re| ≤ ηown)
    (hrepresentative : ∀ a x, ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖(F a).f (emb x) -
        (F (binRepresentative width jet (mergedLabel width jet a))).f (emb x)‖ ≤ ηbin)
    (hroots : ∀ a l t, ‖base l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F a).f (emb (base l t))).re / B
      eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (P a) = 0 ∧
      if pos a then
        19 / 20 * s a ≤ eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ∧
        eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ≤ 21 / 20 * s a
      else
        19 / 20 * s a ≤ -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ∧
        -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 (P a)) ≤ 21 / 20 * s a) :
    ∃ (Q : binLabels width jet → MvPolynomial (Fin 4) ℝ) (sq m₀ : binLabels width jet → ℝ),
      (∀ b, Q b = P (binRepresentative width jet b) ∨
        Q b = pderiv 3 (P (binRepresentative width jet b))) ∧
      (∀ b, sq b = s (binRepresentative width jet b) ∨
        sq b = |qc (P (binRepresentative width jet b))|) ∧
      (∀ b, (Q b).totalDegree ≤ 2 ∧ 0 < sq b ∧ 0 ≤ m₀ b ∧
        m₀ b ≤ 85 * sq b * ((ηown + ηbin) / B) ∧ |qc (Q b)| * m₀ b ≤ (sq b) ^ 2 / 40) ∧
      ∀ a l, l ∈ A a → l ∈ rootTestSet (Q (mergedLabel width jet a))
        (sq (mergedLabel width jet a)) (m₀ (mergedLabel width jet a)) ta tb := by
  obtain ⟨Q, sq, m₀, hQ, hschoice, hdata, hmem⟩ := exists_bin_root_tests_bounded
    F jet width P s pos hP hs A base B ηown ηbin ta tb hB hηown hηbin hsource hrepresentative hroots
  refine ⟨Q, sq, m₀, hQ, hschoice, ?_, hmem⟩
  intro b
  obtain ⟨hdegree, hsq, hm₀, hbound, hcurv, _⟩ := hdata b
  exact ⟨hdegree, hsq, hm₀, hbound, hcurv⟩

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
