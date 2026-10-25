import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Bridge
import Submission.Obl.k4_physical_parent_potential_candidates.GraphPointwiseConic
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Taylor

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MeasureTheory FubiniJets FubiniHessian
open scoped ENNReal

noncomputable section

namespace MeasureNorming

/-- Density relative to the unchanged total mass turns a retained fraction
into a genuine volume floor. -/
theorem volume_floor_of_mass
    {μ : Measure Base} (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    {A θ : ℝ} (hA : 0 < A)
    (hdom : ∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E)
    {E : Set Base} (hE : MeasurableSet E) (hmass : ENNReal.ofReal θ*μ univ ≤ μ E) :
    ENNReal.ofReal (θ/A) ≤ volume E := by
  have hh : ENNReal.ofReal θ*μ univ ≤ (ENNReal.ofReal A*volume E)*μ univ := by
    exact hmass.trans ((hdom E hE).trans_eq (by ring))
  have hc := (ENNReal.mul_le_mul_iff_left hμ0 hμfin).mp hh
  rw [ENNReal.ofReal_div_of_pos hA]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top).mpr
  simpa only [mul_comm] using hc

/-- Remez norming from a set carrying half the original measure. -/
theorem dense_bound_of_half_mass
    {D J : ℕ} (hjet : DenseJetBound D J) {f : Base → ℝ} (hext : HasRealExtension D f)
    {μ : Measure Base} (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    {A v : ℝ} (hA : 2 ≤ A) (hv : 0 ≤ v)
    (hdom : ∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E)
    {E : Set Base} (hE : MeasurableSet E) (hsub : E ⊆ Metric.closedBall (0:Base) 1)
    (hmass : μ univ/2 ≤ μ E) (hsmall : ∀ x ∈ E, |f x| ≤ v) :
    ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Metric.closedBall (0:Base) 2,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (2*A)^J*v := by
  have hA0 : 0 < A := by linarith
  have hvol : ENNReal.ofReal ((2*A)⁻¹) ≤ volume E := by
    have hm : ENNReal.ofReal ((1:ℝ)/2)*μ univ ≤ μ E := by
      simpa [div_eq_mul_inv, mul_comm] using hmass
    convert volume_floor_of_mass hμ0 hμfin hA0 hdom hE hm using 1
    congr 1
    ring
  exact (hjet (2*A) (by linarith) f hext).1 E v hE hsub hvol hv hsmall

/-- Almost-everywhere algebraic smallness for a dominated base measure
controls all jets on the enlarged ball. -/
theorem dense_bound_of_ae
    {D J : ℕ} (hjet : DenseJetBound D J) {f : Base → ℝ} (hext : HasRealExtension D f)
    (hcont : ContinuousOn f (Metric.closedBall (0:Base) (1/2)))
    {μ : Measure Base} (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    {A v : ℝ} (hA : 2 ≤ A) (hv : 0 ≤ v)
    (hdom : ∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E)
    (hsupport : μ (Metric.closedBall (0:Base) (1/2))ᶜ = 0)
    (hsmall : ∀ᵐ x ∂μ, |f x| ≤ v) :
    ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Metric.closedBall (0:Base) 2,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (2*A)^J*v := by
  let E := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧ |f x| ≤ v}
  have hEm : MeasurableSet E :=
    (hcont.abs.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic).measurableSet
  have hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0:Base) (1/2) := by
    rw [ae_iff]
    exact hsupport
  have heq : E =ᵐ[μ] univ := by
    filter_upwards [hs, hsmall] with x hx hf
    exact propext ⟨fun _ => mem_univ x, fun _ => ⟨hx, hf⟩⟩
  have hmass : μ univ/2 ≤ μ E := by
    rw [measure_congr heq]
    calc
      _ ≤ μ univ/2+μ univ/2 := le_add_right le_rfl
      _ = _ := ENNReal.add_halves _
  exact dense_bound_of_half_mass hjet hext hμ0 hμfin hA hv hdom hEm
    (fun x hx => Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ)/2 ≤ 1) hx.1)
    hmass (fun x hx => hx.2)

/-- The low-Hessian part of a closed ball is measurable even though the
actual iterated derivatives need only be continuous on the ambient open ball. -/
theorem measurable_hessian_sublevel
    {f : Base → ℝ} (hf : ContDiffOn ℝ 6 f (Metric.ball (0:Base) 3)) (δ : ℝ) :
    MeasurableSet {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      ∀ i j, |hessian f x i j| ≤ δ} := by
  have hc (i j : Fin 3) : ContinuousOn (fun x => |hessian f x i j|)
      (Metric.closedBall (0:Base) (1/2)) :=
    ((contDiffOn_jet Metric.isOpen_ball hf (M := 0) (by norm_num) ![i,j]).continuousOn.mono
      (Metric.closedBall_subset_ball (by norm_num : (1:ℝ)/2 < 3))).abs
  have hs (i j : Fin 3) := (hc i j).preimage_isClosed_of_isClosed
    Metric.isClosed_closedBall (isClosed_Iic : IsClosed (Iic δ))
  convert (isClosed_iInter fun i => isClosed_iInter fun j => hs i j).measurableSet using 1
  ext x
  simp only [mem_setOf_eq, mem_iInter, mem_inter_iff, mem_preimage, mem_Iic]
  constructor
  · intro hx i j
    exact ⟨hx.1, hx.2 i j⟩
  · intro hx
    exact ⟨(hx 0 0).1, fun i j => (hx i j).2⟩

/-- A coordinate Hessian bound controls the full second-derivative norm. -/
theorem hessian_norm_of_entries (f : Base → ℝ) (x : Base) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ i j, |hessian f x i j| ≤ δ) : ‖iteratedFDeriv ℝ 2 f x‖ ≤ 9*δ := by
  have hb' (α : Fin 2 → Fin 3) :
      |iteratedFDeriv ℝ 2 f x (fun k =>
        Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 (α k))| ≤ δ := by
    have hh := hb (α 0) (α 1)
    rw [hessian_entry_eq] at hh
    convert hh using 1
    congr 2
    funext i
    fin_cases i <;> exact (basis_eq_e3 _).symm
  have hh := Submission.Obl.k4_approximate_conic_taylor_decomposition.norm_le_of_basis _ hδ hb'
  norm_num at hh
  exact hh

/-- A normalized nonaffine graph cannot have a tiny Hessian on a set
carrying half a dominated measure. This supplies the mass for a regular patch. -/
theorem hessian_sublevel_mass_lt_half
    {D J : ℕ} (hjet : DenseJetBound D J) {g : Base → ℝ}
    (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    (hext : ∀ i j, HasRealExtension D (fun x => hessian g x i j))
    (hnon : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0:Base) 1, 1 ≤ |g u-c-L u|)
    {μ : Measure Base} (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    {A : ℝ} (hA : 2 ≤ A)
    (hdom : ∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E) :
    μ {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      ∀ i j, |hessian g x i j| ≤ (100*(2*A)^J)⁻¹} < μ univ/2 := by
  let δ := (100*(2*A)^J)⁻¹
  let E := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧ ∀ i j, |hessian g x i j| ≤ δ}
  have hA0 : 0 < A := by linarith
  have hpow : 0 < (2*A)^J := by positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hEm : MeasurableSet E := measurable_hessian_sublevel hg δ
  by_contra hmass
  have hmass' : μ univ/2 ≤ μ E := le_of_not_gt hmass
  have hb (i j : Fin 3) : ∀ x ∈ Metric.closedBall (0:Base) 2,
      |hessian g x i j| ≤ (2*A)^J*δ := by
    have hh := dense_bound_of_half_mass hjet (hext i j) hμ0 hμfin hA hδ hdom hEm
      (fun x hx => Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ)/2 ≤ 1) hx.1)
      hmass' (fun x hx => hx.2 i j) 0 (by decide)
    intro x hx
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh x hx
  have hB : ∀ x ∈ Metric.closedBall (0:Base) 1, ‖iteratedFDeriv ℝ 2 g x‖ ≤ 9/100 := by
    intro x hx
    have hh := hessian_norm_of_entries g x (mul_nonneg (pow_nonneg (by linarith) J) hδ)
      (fun i j => hb i j x (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) hx))
    apply hh.trans_eq
    dsimp only [δ]
    field_simp
  obtain ⟨u, hu, hna⟩ := hnon (g 0) (fderiv ℝ g 0)
  have ht := Submission.Obl.k4_approximate_conic_taylor_decomposition.abs_sub_radial_taylor_le
    (by decide : 0 < 2) (hg.of_le (by norm_num)) hB hu
  norm_num [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    Nat.factorial] at ht
  have he : g u-(g 0+fderiv ℝ g 0 u) = g u-g 0-fderiv ℝ g 0 u := by ring
  rw [he] at ht
  linarith

/-- At least half the unchanged base measure has a quantitatively
nonzero normalized Hessian. -/
theorem large_hessian_mass
    {D J : ℕ} (hjet : DenseJetBound D J) {g : Base → ℝ}
    (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    (hext : ∀ i j, HasRealExtension D (fun x => hessian g x i j))
    (hnon : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0:Base) 1, 1 ≤ |g u-c-L u|)
    {μ : Measure Base} (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    {A : ℝ} (hA : 2 ≤ A)
    (hdom : ∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E)
    (hsupport : μ (Metric.closedBall (0:Base) (1/2))ᶜ = 0) :
    MeasurableSet {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      ∃ i j, (100*(2*A)^J)⁻¹ < |hessian g x i j|} ∧
    μ univ/2 ≤ μ {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      ∃ i j, (100*(2*A)^J)⁻¹ < |hessian g x i j|} := by
  let E := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
    ∀ i j, |hessian g x i j| ≤ (100*(2*A)^J)⁻¹}
  let G := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
    ∃ i j, (100*(2*A)^J)⁻¹ < |hessian g x i j|}
  have hEm : MeasurableSet E := measurable_hessian_sublevel hg _
  have hGeq : G = Metric.closedBall (0:Base) (1/2) ∩ Eᶜ := by
    ext x
    simp only [G, E, mem_setOf_eq, mem_inter_iff, mem_compl_iff, not_and, not_forall, not_le]
    tauto
  have hsmall : μ E < μ univ/2 := hessian_sublevel_mass_lt_half hjet hg hext hnon hμ0 hμfin hA hdom
  have hhalf : μ univ/2 ≤ μ Eᶜ := by
    by_contra hh
    have hlt := ENNReal.add_lt_add hsmall (lt_of_not_ge hh)
    rw [measure_add_measure_compl hEm, ENNReal.add_halves] at hlt
    exact lt_irrefl _ hlt
  refine ⟨?_, ?_⟩
  · change MeasurableSet G
    rw [hGeq]
    exact (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0:Base) (1/2))).measurableSet.inter hEm.compl
  · change μ univ/2 ≤ μ G
    rw [hGeq, inter_comm, measure_inter_conull hsupport]
    exact hhalf

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
