/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SampleAgreement.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleSheets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.ChosenSourceFit
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.TrajectoryAffine

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample

open MeasureTheory Set Metric MvPolynomial

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

/-- A retained pair with agreeing matching sheets has the exact localPair
predicate, including the fit on its actual short source trajectory. -/
theorem localPair_of_matching_agreement (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 0 < Nk)
    {mesh r out M₀ : ℝ} (hmesh : 0 < mesh) (hmr : mesh ≤ r / 2)
    (hpos : ∀ p : s.Active,
      DiscPosOn (s.P (s.src p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r ∧
      DiscPosOn (s.P (s.wit p)) (gridCenter mesh (gridLabel mesh (s.sourceBase p))) r)
    (hrad : 2 * Nk ^ (-out) ≤ r / 2)
    (hfloor : Nk ^ (-out) ≤ Nk ^ (-a))
    (herror : 4 * (δ Nk L * Nk ^ a) / Nk ^ (-a) ≤ δ Nk L * Nk ^ out)
    (hslope : 2 * Nk ^ a * (Nk ^ (-out) / 100) ≤ Nk ^ (-a) / 2)
    (hM₀ : M₀ ≤ δ Nk L * Nk ^ out) (p : s.Active)
    (hagree : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
      ‖(s.toPairTests hω hNk hmesh (by linarith) hpos).toDiscSetup.φ
          ((s.toPairTests hω hNk hmesh (by linarith) hpos).toDiscSetup.src p) (emb y) -
        (s.toPairTests hω hNk hmesh (by linarith) hpos).toDiscSetup.φ
          ((s.toPairTests hω hNk hmesh (by linarith) hpos).toDiscSetup.wit p) (emb y)‖ < M₀) :
    localPair Nk out (δ Nk L) ((2 : ℝ) ^ s.T) (s.P (s.src p)) (s.P (s.wit p))
      (s.sourceBase p)
      (base s.T (s.j (s.frame (s.src p)) : ℝ) s.κ (s.c (s.frame (s.src p)))
        (s.u (s.frame (s.src p))) (s.Q (s.frame (s.src p))) (s.point p).1)
      (fun t => Bk (s.γ (s.frame (s.src p))) * (x (s.point p).1 t) 3)
      (s.point p).2.1 (s.block (s.frame (s.src p))) := by
  let b := s.frame (s.src p)
  let zline := base s.T (s.j b : ℝ) s.κ (s.c b) (s.u b) (s.Q b) (s.point p).1
  let wline : ℝ → ℝ := fun t => Bk (s.γ b) * (x (s.point p).1 t) 3
  let t₀ := (s.point p).2.1
  let I := s.block b
  let c₀ := gridCenter mesh (gridLabel mesh (s.sourceBase p))
  let σ := sgn (realDerivativeTrace (s.P (s.src p)) zline wline t₀)
  let σ' := sgn (realDerivativeTrace (s.P (s.wit p)) zline wline t₀)
  have hr : 0 < r := by linarith
  have hq : 0 < (2 : ℝ) ^ s.T := by positivity
  have hpow : 0 < Nk ^ (-out) := Real.rpow_pos_of_pos hNk _
  have hA : 0 ≤ Nk ^ a := Real.rpow_nonneg hNk.le _
  have hB : 0 < Nk ^ (-a) := Real.rpow_pos_of_pos hNk _
  have hV : 0 ≤ δ Nk L * Nk ^ a := by unfold δ; positivity
  have hS := (s.hS (s.src p)).2.2 _ (s.row_source _ p.property)
  have ht₀ : t₀ ∈ I := hS.2.2.2.1
  have htst := ((s.hH _ _).2 _ (s.witness_mem p)).2.2.2.2.2
  have hres : ∀ t ∈ I, |realTrace (s.P (s.src p)) zline wline t| ≤ δ Nk L * Nk ^ a :=
    fun t ht => (htst.2 t ht).1
  have hderivbound : ∀ t ∈ I, |realDerivativeTrace (s.P (s.src p)) zline wline t| ≤ Nk ^ a :=
    fun t ht => (htst.2 t ht).2
  have hzc : ‖s.sourceBase p - c₀‖ ≤ r / 2 :=
    (norm_sub_gridCenter_le hmesh _).trans hmr
  have hfit : ∀ t ∈ I ∩ Icc (t₀ - Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T))
      (t₀ + Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T)),
      ‖(wline t : ℂ) - simpleSheet (s.P (s.src p)) σ (emb (zline t))‖ ≤ δ Nk L * Nk ^ out := by
    obtain ⟨m, d, hmd⟩ := source_derivative_affine (s.P (s.src p)) (s.hP _).1
      s.T (s.j b : ℝ) s.κ (Bk (s.γ b)) (s.c b) (s.u b) (s.Q b) (s.point p).1
    have hderiv : ∀ t ∈ I, realDerivativeTrace (s.P (s.src p)) zline wline t = m * t + d :=
      fun t _ => hmd t
    have hσ : σ * (m * t₀ + d) = |m * t₀ + d| := by
      rw [← hderiv t₀ ht₀]
      exact sgn_mul_self _
    have hdisc : ∀ t ∈ I ∩ Icc (t₀ - Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T))
        (t₀ + Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T)),
        0 ≤ eval (fun i => zline t i) (disc (s.P (s.src p))) := by
      intro t ht
      apply (disc_pos_of_discPosOn (hpos p).1 ?_).le
      have hdist : |t - t₀| ≤ Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T) :=
        abs_le.mpr ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
      have hlip : ‖zline t - s.sourceBase p‖ ≤ (2 : ℝ) ^ s.T * |t - t₀| :=
        (hS.2.2.2.2 t ht.1).2.2.2 t₀ ht₀
      calc ‖zline t - c₀‖ ≤ ‖zline t - s.sourceBase p‖ + ‖s.sourceBase p - c₀‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (2 : ℝ) ^ s.T * (Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T)) + r / 2 :=
          add_le_add (hlip.trans (mul_le_mul_of_nonneg_left hdist hq.le)) hzc
        _ = Nk ^ (-out) / 100 + r / 2 := by field_simp [hq.ne']
        _ < 8 * r := by linarith
    have hinterval : ((s.j b : ℝ) + 1) / (2 : ℝ) ^ s.T - (s.j b : ℝ) / (2 : ℝ) ^ s.T =
        ((2 : ℝ) ^ s.T)⁻¹ := by field_simp; ring
    have hse : (s.j b : ℝ) / (2 : ℝ) ^ s.T < ((s.j b : ℝ) + 1) / (2 : ℝ) ^ s.T := by
      apply (div_lt_div_iff_of_pos_right hq).mpr
      linarith
    have hsmall : (2 * Nk ^ a /
        (((s.j b : ℝ) + 1) / (2 : ℝ) ^ s.T - (s.j b : ℝ) / (2 : ℝ) ^ s.T)) *
        (Nk ^ (-out) / (100 * (2 : ℝ) ^ s.T)) ≤ Nk ^ (-a) / 2 := by
      rw [hinterval]
      convert hslope using 1 <;> field_simp [hq.ne']
    have hsourcefloor : Nk ^ (-a) ≤ |m * t₀ + d| := by
      rw [← hderiv t₀ ht₀]
      exact (s.chosen_tests p _ (Or.inl rfl)).2.1
    have hf := chosen_simpleSheet_source_fit (s.P (s.src p)) (s.hP _).1 zline wline
      hse hA hB hV (sgn_sq _) hderiv hderivbound hsourcefloor hσ hres hdisc hsmall
    intro t ht
    exact (hf t ht).trans herror
  have hnear (i : Fin s.m) (hi : i = s.src p ∨ i = s.wit p) :
      ‖simpleSheet (s.P i) (sgn (realDerivativeTrace (s.P i) zline wline t₀))
        (emb (s.sourceBase p)) - (wline t₀ : ℂ)‖ ≤ δ Nk L * Nk ^ out := by
    have hposi : DiscPosOn (s.P i) c₀ r := by
      rcases hi with rfl | rfl
      · exact (hpos p).1
      · exact (hpos p).2
    have ht := s.chosen_tests p i hi
    have hne : realDerivativeTrace (s.P i) zline wline t₀ ≠ 0 := by
      intro hz
      have := ht.2.1
      change Nk ^ (-a) ≤ |realDerivativeTrace (s.P i) zline wline t₀| at this
      rw [hz, abs_zero] at this
      linarith
    have he := simpleSheet_error (s.P i) (s.hP i).1 _ (sgn_sq _) (s.sourceBase p)
      (wline t₀) (disc_pos_of_discPosOn hposi (by linarith)).le hne (sgn_mul_self _)
    refine he.trans ((s.nearest_root_error hNk p i hi).trans ?_)
    change 2 * (δ Nk L * Nk ^ a) / Nk ^ (-a) ≤ δ Nk L * Nk ^ out
    calc _ ≤ 4 * (δ Nk L * Nk ^ a) / Nk ^ (-a) := by gcongr; norm_num
      _ ≤ _ := herror
  apply localPair_of_matchSheets (s.hP _).1 (s.hP _).1 hr hzc
    (by linarith) hrad (hpos p).1 (hpos p).2 (sgn_sq _) (sgn_sq _)
    (hfloor.trans (((s.chosen_tests p _ (Or.inl rfl)).2.2.2 hcv).trans (le_abs_self _)))
    (hfloor.trans (((s.chosen_tests p _ (Or.inr rfl)).2.2.2 hcv).trans (le_abs_self _)))
    (hnear _ (Or.inl rfl)) (hnear _ (Or.inr rfl)) hM₀
  · intro y hy
    have hh := hagree y hy
    change ‖matchSheet (s.P (s.src p)) c₀ r (if nonnegBool _ then 1 else -1) (emb y) -
      matchSheet (s.P (s.wit p)) c₀ r (if nonnegBool _ then 1 else -1) (emb y)‖ < M₀ at hh
    rw [sign_eq_sgn, sign_eq_sgn] at hh
    exact hh
  · exact hfit

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample
