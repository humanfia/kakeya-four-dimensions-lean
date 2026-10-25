import Submission.Obl.k4_pair_anchor_jet_bins.Geometry
import Submission.Obl.k4_pair_anchor_jet_bins.BinChoice
import Submission.Obl.k4_pair_anchor_jet_bins.Return
import Submission.Obl.k4_pair_anchor_jet_bins.Parameters
import Submission.Obl.k4_pair_anchor_jet_bins.RealComplex
import Submission.Obl.k4_pair_anchor_jet_bins.Transfer
import Submission.Obl.k4_pair_anchor_jet_bins.Trajectory
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Geometry

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Set Metric MvPolynomial Submission.Lib.K4QuadraticSheets

private lemma emb_norm (z : R3) : ‖emb z‖ = ‖z‖ :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).norm_map z

private lemma vertices_norm {z α : R3} (hz : ‖z‖ ≤ 1 / 8)
    (hα : α ∈ closedBall (0 : R3) (1 / 8)) {σ : ℂ}
    (hσ : σ ∈ closedBall (1 / 2 : ℂ) (1 / 4)) :
    ‖emb z‖ ≤ 1 ∧ ‖emb z + σ • (emb α - emb z)‖ ≤ 1 ∧ ‖emb α‖ ≤ 1 := by
  have hα' : ‖α‖ ≤ 1 / 8 := by simpa using hα
  have hσ' := (Submission.Obl.k4_quadratic_discriminant_safe_paths.detour_norms hσ).1
  have hdiff : ‖emb α - emb z‖ ≤ 1 / 4 := by
    have hh := (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).isometry.dist_eq α z
    rw [dist_eq_norm, dist_eq_norm] at hh
    change ‖emb α - emb z‖ = ‖α - z‖ at hh
    rw [hh]
    exact (norm_sub_le α z).trans (by linarith)
  refine ⟨by rw [emb_norm]; linarith, ?_, by rw [emb_norm]; linarith⟩
  calc
    _ ≤ ‖emb z‖ + ‖σ • (emb α - emb z)‖ := norm_add_le _ _
    _ = ‖z‖ + ‖σ‖ * ‖emb α - emb z‖ := by rw [emb_norm, norm_smul]
    _ ≤ 1 / 8 + 1 * (1 / 4) :=
      add_le_add hz (mul_le_mul hσ' hdiff (norm_nonneg _) zero_le_one)
    _ ≤ 1 := by norm_num

private lemma small_ball_norm {z : R3} (hz : ‖z‖ ≤ 1 / 8) {T : ℝ} (hT : 2 ≤ T)
    {ζ : E3} (hζ : ζ ∈ closedBall (emb z) ((8 * T)⁻¹)) : ‖ζ‖ ≤ 1 := by
  have hsmall : (8 * T)⁻¹ ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith : 0 < 8 * T) (by norm_num)).mpr (by linarith)
      _ = _ := by norm_num
  have hζ' : ‖ζ - emb z‖ ≤ (8 * T)⁻¹ := by simpa only [mem_closedBall, dist_eq_norm] using hζ
  have hh := norm_add_le (ζ - emb z) (emb z)
  rw [sub_add_cancel, emb_norm] at hh
  linarith

private lemma norm_eval_snoc_real {Cs : ℕ} {k A₀ : ℝ} (g : Geometry Cs k A₀)
    (P : Test) (z : R3) (w : ℝ) :
    ‖eval (Fin.snoc (fun i => emb z i) (w : ℂ)) (P.map (algebraMap ℝ ℂ))‖ =
      |eval (Fin.snoc (fun i => z i) w) P| := by
  have heq : (fun i => ((Fin.snoc (fun j => z j) w : Fin 4 → ℝ) i : ℂ)) =
      (Fin.snoc (fun i => emb z i) (w : ℂ) : Fin 4 → ℂ) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change ((Fin.snoc (fun j => z j) w : Fin 4 → ℝ) (Fin.last 3) : ℂ) =
        (Fin.snoc (fun i => emb z i) (w : ℂ) : Fin 4 → ℂ) (Fin.last 3)
      simp only [Fin.snoc_last]
    · simp [emb]
  simpa only [heq] using g.real_eval 4 P (Fin.snoc (fun i => z i) w)

/-- Assemble the analytic kernel from the uniform discriminant geometry. -/
theorem scaleKernel_of_geometry (hC : Continuation) {Cs : ℕ} {k A₁ : ℝ}
    (g : Geometry Cs k A₁) : ScaleKernel Cs := by
  classical
  obtain ⟨J, C₁, C₂, hC₁, hC₂, hreturn⟩ := bin_return hC
  obtain ⟨CF, hCF, hforward⟩ := continuation_bin_pair hC J
  obtain ⟨C₀, hC₀, hcompare⟩ := exists_local_real_complex_difference_bound 3 2
  obtain ⟨CR, CK, CB, CV, V, A₀, hCR, hCK, hE, hCV, hnum⟩ :=
    choose_scale_parameters J k CF C₁ C₂ C₀ A₁ g.exponent hCF hC₁ hC₂
  refine ⟨J, CR, CK, CB, A₀, hCR, hCK, ?_⟩
  intro A δ q hA₀ hδ hδ1 hq P P' z α σ zline wline t₀ I hP hP' hz ht₀ hzline hlip
    hpair hα hσ hsafe
  obtain ⟨hA₁, hA, hwidth₀, hmesh₀, hretpow, hfinalpow, hradius, htimefit⟩ := hnum A hA₀
  have hA0 : 0 < A := by linarith
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA0
  have hT : 2 ≤ A ^ k := (g.scale A hA₁).2.1
  have hT0 : 0 < A ^ k := by linarith
  have hTinv : 0 < (A ^ k)⁻¹ := inv_pos.mpr hT0
  have hlocal : (A ^ k)⁻¹ ≤ A⁻¹ := (g.scale A hA₁).2.2
  have hsmall : (8 * A ^ k)⁻¹ < (A ^ k)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) hT0]
    linarith
  have hρ : 0 < A ^ (-(Cs : ℝ)) := Real.rpow_pos_of_pos hA0 _
  have hαtube : emb α ∈ thickening (A ^ (-(Cs : ℝ))) (safePath z α σ) :=
    self_subset_thickening hρ _ (Or.inr (right_mem_segment ℝ _ _))
  have halow := hsafe (emb α) hαtube
  have halowP : A ^ (-(Cs : ℝ)) ≤ |eval (fun i => α i) (disc P)| := by
    rw [← g.real_eval 3 (disc P) (fun i => α i)]
    exact halow.1
  have halowP' : A ^ (-(Cs : ℝ)) ≤ |eval (fun i => α i) (disc P')| := by
    rw [← g.real_eval 3 (disc P') (fun i => α i)]
    exact halow.2
  obtain ⟨hP0, hpertP⟩ := g.anchor A hA₁ δ P hP α hα halowP
  obtain ⟨hP'0, hpertP'⟩ := g.anchor A hA₁ δ P' hP' α hα halowP'
  have hPdeg : (P.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 := (g.degree P).trans hP.1
  have hP'deg : (P'.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 := (g.degree P').trans hP'.1
  obtain ⟨S, S', hS, hS'⟩ := g.sqrt A hA₁ δ P P' hP hP' z α σ hsafe
  obtain ⟨_, _, f₀, f'₀, hspec, _, _, hreal, hfit⟩ := hpair
  have hf₀ := hspec P f₀ (Or.inl ⟨rfl, rfl⟩)
  have hf'₀ := hspec P' f'₀ (Or.inr ⟨rfl, rfl⟩)
  have hreal' : ∀ x : R3, x ∈ closedBall z A⁻¹ → ‖f₀ (emb x) - f'₀ (emb x)‖ ≤ δ * A := by
    intro x hx
    exact hreal x ((closedBall_subset_closedBall (by linarith)) hx)
  have hcomplex := hcompare f₀ f'₀ (P.map (algebraMap ℝ ℂ)) (P'.map (algebraMap ℝ ℂ))
    hP0 hP'0 hPdeg hP'deg z A⁻¹ (δ * A) hAinv (mul_pos hδ hA0)
    hf₀.1 hf'₀.1 (fun ζ hζ => (hf₀.2.1 ζ hζ).1)
    (fun ζ hζ => (hf'₀.2.1 ζ hζ).1) hreal'
  have hstart : ball (emb z) (A ^ k)⁻¹ ⊆ ball (emb z) (8 * A⁻¹) :=
    ball_subset_ball (by linarith)
  have hclose : ∀ ζ ∈ closedBall (emb z) ((8 * A ^ k)⁻¹),
      ‖f₀ ζ - f'₀ ζ‖ ≤ C₀ * (δ * A) := by
    intro ζ hζ
    exact hcomplex ζ ((closedBall_subset_closedBall (by linarith)) hζ)
  have hw : 0 < δ * A ^ CB := mul_pos hδ (Real.rpow_pos_of_pos hA0 _)
  have hwidth : (A ^ k) ^ CF * (C₀ * (δ * A)) ≤ δ * A ^ CB := by
    calc
      _ = δ * (C₀ * A ^ (k * CF + 1)) := by
        rw [← Real.rpow_mul hA0.le, Real.rpow_add hA0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwidth₀ hδ.le
  have hvertices := vertices_norm hz hα hσ
  obtain ⟨f, hfs, hfa, hff₀, hbin, β', hβ', hnear⟩ := hforward (A ^ k) hT P P' z α σ
    hvertices.1 hvertices.2.1 hvertices.2.2 hPdeg hP0 hP'deg hP'0 S S' hS.1 hS.2 hS'.1 hS'.2
    (by intro R hR; simp only [mem_insert_iff, mem_singleton_iff] at hR
        rcases hR with rfl | rfl; exact hpertP; exact hpertP')
    f₀ f'₀ (hf₀.1.continuousOn.mono hstart) (hf'₀.1.continuousOn.mono hstart)
    (fun ζ hζ => ⟨(hf₀.2.1 ζ (hstart hζ)).1, (hf'₀.2.1 ζ (hstart hζ)).1⟩)
    (C₀ * (δ * A)) (δ * A ^ CB) (by positivity) hw hwidth hclose
  refine ⟨flatJetBin J (δ * A ^ CB) f (emb α), hbin, β', hβ', hnear, ?_⟩
  intro R hR hlower hbinR t ht htime
  have hRdeg : (R.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 := (g.degree R).trans hR.1
  have hqc := g.qc A δ R hR
  obtain ⟨hR0, hpertR⟩ := g.anchor A hA₁ δ R hR α hα hlower
  have hcanon := fun ε : Bool => canonBranch_spec hRdeg hR0 hpertR ε
  have hαnorm : ‖α‖ ≤ 1 / 8 := by simpa using hα
  have hder : ∀ (ε : Bool) ζ, ζ ∈ closedBall (emb α) ((8 * A ^ k)⁻¹) →
      ‖eval (Fin.snoc (fun i => ζ i) (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε ζ))
        (pderiv (Fin.last 3) (R.map (algebraMap ℝ ℂ)))‖ ≤ A ^ (2 : ℕ) := by
    intro ε ζ hζ
    exact g.root_deriv A hA₁ δ R hR ζ _ (small_ball_norm hαnorm hT hζ)
      (((hcanon ε).1.2.2.2 ζ (mem_ball.mpr ((mem_closedBall.mp hζ).trans_lt hsmall))).1)
  have hmesh : (3 : ℝ) ^ J * (2 * (δ * A ^ CB)) ≤ δ * A ^ V := by
    calc
      _ = δ * ((2 * (3 : ℝ) ^ J) * A ^ CB) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmesh₀ hδ.le
  have hbound := hreturn A δ k V CV (δ * A ^ CB) (by linarith) hδ hT hw hmesh hE hretpow
    P R z α σ hvertices.1 hvertices.2.1 hvertices.2.2 hRdeg hqc f hfs hfa hcanon hder hbinR
  obtain ⟨hpoint, htime'⟩ := trajectory_point_control hq hradius htimefit (zline t) z (hlip t ht) htime
  have hpointB : emb (zline t) ∈ ball (emb z) (A ^ k)⁻¹ :=
    mem_ball.mpr ((mem_closedBall.mp hpoint).trans_lt hsmall)
  have hfit' : ‖(wline t : ℂ) - f (emb (zline t))‖ ≤ δ * A := by
    rw [hff₀ _ hpointB]
    exact hfit t ⟨ht, htime'⟩
  have hdiscR := g.disc A hA₁ δ R hR (emb (zline t)) (small_ball_norm hz hT hpoint)
  obtain ⟨hvalue, hderiv⟩ := transfer_hidden_value hRdeg hδ hA0.le
    (Real.rpow_nonneg hA0.le CV) (sq_nonneg A) hqc (fun i => emb (zline t) i)
    (wline t : ℂ) (f (emb (zline t))) hdiscR (hbound _ hpoint) hfit'
  have htransfer := transfer_expression_bound (by linarith : 1 ≤ A) hCV hfinalpow
  have hv := hvalue.trans (mul_le_mul_of_nonneg_left htransfer.1 hδ.le)
  have hd := hderiv.trans htransfer.2
  constructor
  · simpa only [norm_eval_snoc_real g R (zline t) (wline t)] using hv
  · simpa only [show Fin.last 3 = (3 : Fin 4) from rfl, pderiv_map,
      norm_eval_snoc_real g (pderiv (3 : Fin 4) R) (zline t) (wline t)] using hd

end Submission.Obl.k4_pair_anchor_jet_bins
