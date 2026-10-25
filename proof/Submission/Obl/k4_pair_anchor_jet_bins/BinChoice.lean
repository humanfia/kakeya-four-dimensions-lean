import Submission.Obl.k4_pair_anchor_jet_bins.Bins

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Submission.Lib.K4QuadraticSheets

/-- Forward continuation chooses a source bin and a neighbouring witness bin. -/
theorem continuation_bin_pair (hC : Continuation) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ (P P' : Test) (z α : R3) (σ : ℂ),
    ‖emb z‖ ≤ 1 → ‖emb z + σ • (emb α - emb z)‖ ≤ 1 → ‖emb α‖ ≤ 1 →
    (P.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 → P.map (algebraMap ℝ ℂ) ≠ 0 →
    (P'.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 → P'.map (algebraMap ℝ ℂ) ≠ 0 →
    ∀ S S' : E3 → ℂ,
    AnalyticOnNhd ℂ S (Metric.thickening T⁻¹ (safePath z α σ)) →
    (∀ ζ ∈ Metric.thickening T⁻¹ (safePath z α σ),
      S ζ ^ 2 = qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) ∧
      qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) ≠ 0) →
    AnalyticOnNhd ℂ S' (Metric.thickening T⁻¹ (safePath z α σ)) →
    (∀ ζ ∈ Metric.thickening T⁻¹ (safePath z α σ),
      S' ζ ^ 2 = qdisc (P'.map (algebraMap ℝ ℂ)) (fun i => ζ i) ∧
      qdisc (P'.map (algebraMap ℝ ℂ)) (fun i => ζ i) ≠ 0) →
    (∀ R ∈ ({P, P'} : Set Test), ∀ ζ ∈ Metric.ball (emb α) T⁻¹,
      ‖qdisc (R.map (algebraMap ℝ ℂ)) (fun i => ζ i) -
        qdisc (R.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖ <
        ‖qdisc (R.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖) →
    ∀ f₀ f'₀ : E3 → ℂ,
    ContinuousOn f₀ (Metric.ball (emb z) T⁻¹) →
    ContinuousOn f'₀ (Metric.ball (emb z) T⁻¹) →
    (∀ ζ ∈ Metric.ball (emb z) T⁻¹,
      MvPolynomial.eval (Fin.snoc (fun i => ζ i) (f₀ ζ)) (P.map (algebraMap ℝ ℂ)) = 0 ∧
      MvPolynomial.eval (Fin.snoc (fun i => ζ i) (f'₀ ζ)) (P'.map (algebraMap ℝ ℂ)) = 0) →
    ∀ V w : ℝ, 0 ≤ V → 0 < w → T ^ C * V ≤ w →
    (∀ ζ ∈ Metric.closedBall (emb z) ((8 * T)⁻¹), ‖f₀ ζ - f'₀ ζ‖ ≤ V) →
    ∃ f : E3 → ℂ,
      SimpleSheet (P.map (algebraMap ℝ ℂ)) f (Metric.thickening T⁻¹ (safePath z α σ)) ∧
      AnalyticOnNhd ℂ f (Metric.thickening T⁻¹ (safePath z α σ)) ∧
      (∀ ζ ∈ Metric.ball (emb z) T⁻¹, f ζ = f₀ ζ) ∧
      flatJetBin J w f (emb α) ∈ bins J w P α ∧
      ∃ β' ∈ bins J w P' α, ∀ i, |flatJetBin J w f (emb α) i - β' i| ≤ 1 := by
  obtain ⟨q, C, hJq, hC0, hmain⟩ := anchor_forward hC J
  refine ⟨C, hC0, ?_⟩
  intro T hT P P' z α σ hz hb hα hP hP0 hP' hP'0 S S' hSa hS hS'a hS' hpert
    f₀ f'₀ hf₀ hf'₀ hroots V w hV hw hwidth hclose
  obtain ⟨f, hfs, hfa, hff₀, ε', hjets⟩ := hmain T hT (emb z)
    (emb z + σ • (emb α - emb z)) (emb α) hz hb hα
    (P.map (algebraMap ℝ ℂ)) (P'.map (algebraMap ℝ ℂ)) hP hP0 hP' hP'0
    S S' hSa hS hS'a hS' (hpert P' (by simp)) f₀ f'₀ hf₀ hf'₀ hroots V hV hclose
  have hTinv : 0 < T⁻¹ := inv_pos.mpr (by linarith)
  have hBc : Metric.ball (emb α) T⁻¹ ⊆ Metric.thickening T⁻¹ (safePath z α σ) :=
    ball_end_subset_tube (emb z) (emb z + σ • (emb α - emb z)) (emb α) T
  obtain ⟨ε, hε⟩ := sheet_eq_canonBranch hP hTinv (hpert P (by simp))
    (hfs.2.2.1.continuousOn.mono hBc) (fun ζ hζ => (hfs.2.2.2 ζ (hBc hζ)).1)
  have hbin : flatJetBin J w f (emb α) = branchBin J w P α ε :=
    flatJetBin_eq_of_eqOn_ball hTinv hε
  refine ⟨f, hfs, hfa, hff₀, ?_, branchBin J w P' α ε', branchBin_mem _ _ _ _ _, ?_⟩
  · rw [hbin]
    exact branchBin_mem _ _ _ _ _
  · exact flatJetBin_near hw (fun j hj => (hjets j (hj.trans hJq)).trans hwidth)

end Submission.Obl.k4_pair_anchor_jet_bins
