-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.UniformExponents.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.ParameterTransfer

/-!
# Uniform parameters from fixed-exponent estimates

Only fixed-exponent estimates are needed as analytic input. Their gains and
error exponents need not be continuous or have a stated uniform lower bound:
exponent stability and compactness supply common positive parameters.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem uniform_separated_furstenberg_on_Icc {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ s ∈ Set.Icc a b, ∃ ε₀ η r₀ : ℝ,
      0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ → SeparatedFurstenbergAt r s ε₀ η) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r σ : ℝ, 0 < r → r ≤ r₀ → σ ∈ Set.Icc a b →
        SeparatedFurstenbergAt r σ ε₀ η := by
  classical
  by_cases hab : a ≤ b
  · let S := Set.Icc a b
    have hfixed (s : S) := h s.1 s.2
    choose eps eta R heps heta hR hcore using hfixed
    let radius (s : S) := min (eps s) (eta s) / 8
    have hradius (s : S) : 0 < radius s :=
      div_pos (lt_min (heps s) (heta s)) (by norm_num)
    obtain ⟨I, hcover⟩ := isCompact_Icc.elim_finite_subcover
      (fun s : S => Metric.ball (s : ℝ) (radius s))
      (fun _ => Metric.isOpen_ball) (by
        intro s hs
        exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Metric.mem_ball_self (hradius ⟨s, hs⟩)⟩)
    have hIne : I.Nonempty := by
      obtain ⟨s, hs, _⟩ := Set.mem_iUnion₂.mp (hcover (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩))
      exact ⟨s, hs⟩
    let e := I.inf' hIne (fun s => eps s / 2)
    let η := I.inf' hIne (fun s => eta s / 2)
    let r₀ := min (1 / 2 : ℝ) (I.inf' hIne R)
    have he : 0 < e := (Finset.lt_inf'_iff hIne).2 (fun s _ => by
      exact div_pos (heps s) (by norm_num))
    have hη : 0 < η := (Finset.lt_inf'_iff hIne).2 (fun s _ => by
      exact div_pos (heta s) (by norm_num))
    have hr₀ : 0 < r₀ := lt_min (by norm_num)
      ((Finset.lt_inf'_iff hIne).2 (fun s _ => hR s))
    refine ⟨e, η, r₀, he, hη, hr₀, ?_⟩
    intro r σ hr hrs hσ
    obtain ⟨s, hs, hnear⟩ := Set.mem_iUnion₂.mp (hcover hσ)
    have hhalf : r ≤ 1 / 2 := hrs.trans (min_le_left _ _)
    have hrsR : r ≤ R s :=
      (hrs.trans (min_le_right _ _)).trans (Finset.inf'_le R hs)
    have hemin : e ≤ eps s / 2 := Finset.inf'_le _ hs
    have hηmin : η ≤ eta s / 2 := Finset.inf'_le _ hs
    have hd : |σ - (s : ℝ)| < radius s := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hnear
    have hde : radius s ≤ eps s / 8 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hdη : radius s ≤ eta s / 8 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    exact separated_furstenberg_exponent_transfer hr hhalf (ha.trans s.2.1)
      (by linarith [heta s]) (by linarith [heps s]) (hcore s r hr hrsR)
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro r σ hr hrs hσ
    exact False.elim (hab (hσ.1.trans hσ.2))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
