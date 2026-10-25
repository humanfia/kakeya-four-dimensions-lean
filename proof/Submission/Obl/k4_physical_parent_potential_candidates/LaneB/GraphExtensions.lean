import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EntryExtensions
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniCleared

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric FubiniHessian
open scoped ContDiff

/-- The actual Hessian and graph-cleared cubic tensor have algebraic real
extensions. The tensor here uses the graph's third derivatives itself. -/
theorem hasRealExtension_graph_entries_of_sqrtRep {D : ℕ}
    {Δ : MvPolynomial (Fin 3) ℂ} (hΔ : Δ.totalDegree ≤ D) (hΔne : Δ ≠ 0)
    {s F : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hs : DifferentiableOn ℂ s (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z)^2 = eval (fun i => z i) Δ)
    (hF : SqrtRep (ball 0 4) s D F)
    {f : Base → ℝ}
    (hf : ∀ x ∈ ball (0:Base) 4, F (DenseJet.realSlice x) = (f x:ℂ)) :
    (∀ i j, HasRealExtension (8*(10000*(D+1))+2) (fun x => hessian f x i j)) ∧
    (∀ i j k, HasRealExtension (8*(10000*(D+1))+2)
      (fun x => clearedCubicError f x i j k)) := by
  let Hc : Fin 3 → Fin 3 → EuclideanSpace ℂ (Fin 3) → ℂ := fun a b z =>
    iteratedFDeriv ℂ 2 F z (fun l => DenseJet.realSlice (FubiniJets.basis (![a,b] l)))
  let Tc : Fin 3 → Fin 3 → Fin 3 → EuclideanSpace ℂ (Fin 3) → ℂ := fun a b c z =>
    iteratedFDeriv ℂ 3 F z (fun l => DenseJet.realSlice (FubiniJets.basis (![a,b,c] l)))
  have hH : ∀ a b, SqrtRep (ball 0 4) s (9*D) (Hc a b) := fun a b =>
    (hF.iteratedFDeriv_apply isOpen_ball hs hΔ hΔne hroot 2 _).mono (by norm_num)
  have hT : ∀ a b c, SqrtRep (ball 0 4) s (27*D) (Tc a b c) := fun a b c =>
    (hF.iteratedFDeriv_apply isOpen_ball hs hΔ hΔne hroot 3 _).mono (by norm_num)
  have hreal : ∀ x : Base, ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x:ℂ) :=
    fun x hx => hf x (mem_ball_zero_iff.mpr hx)
  have hHr : ∀ a b, ∀ x : Base, ‖x‖ < 4 → Hc a b (DenseJet.realSlice x) =
      (hessian f x a b : ℂ) := fun a b x hx =>
    complex_jet_on_real_directions (hF.1.of_le le_top) hreal 2 hx _
  have hTr : ∀ a b c, ∀ x : Base, ‖x‖ < 4 → Tc a b c (DenseJet.realSlice x) =
      (cubic f x a b c : ℂ) := fun a b c x hx =>
    complex_jet_on_real_directions (hF.1.of_le le_top) hreal 3 hx _
  refine ⟨fun i j => ?_, fun i j k => ?_⟩
  · exact (hasRealExtension_of_sqrtRep (hΔ.trans (by omega)) hroot (hH i j)
      (fun x hx => hHr i j x (mem_ball_zero_iff.mp hx))).mono_degree (by omega)
  · have hc := SqrtRep.clearedFormula3 hΔ hroot
      (M := fun z => Matrix.of fun a b => Hc a b z)
      (T := fun z a b c => Tc a b c z) hH hT i j k
    refine (hasRealExtension_of_sqrtRep (hΔ.trans (by omega)) hroot hc ?_).mono_degree
      (by omega)
    intro x hx
    have hx' : ‖x‖ < 4 := mem_ball_zero_iff.mp hx
    have hM : (Matrix.of fun a b => Hc a b (DenseJet.realSlice x)) =
        Complex.ofRealHom.mapMatrix (hessian f x) := by
      ext a b
      simp [hHr a b x hx']
    have hTc : (fun a b c => Tc a b c (DenseJet.realSlice x)) =
        fun a b c => Complex.ofRealHom (cubic f x a b c) := by
      funext a b c
      simp [hTr a b c x hx']
    change clearedFormula (Matrix.of fun a b => Hc a b (DenseJet.realSlice x))
      (fun a b c => Tc a b c (DenseJet.realSlice x)) i j k = _
    rw [hM, hTc, ← map_clearedFormula, ← cleared_eq_clearedFormula]
    rfl

/-- Affine subtraction and scalar normalization preserve the algebraic
extensions needed by palette-free analytic restoration. The uniform degree
depends only on the branch presentation degree. -/
theorem hasRealExtension_normalized_graph_entries (D : ℕ) : ∃ D' : ℕ,
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D → Δ ≠ 0 → W ≠ 0 →
    ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ), DifferentiableOn ℂ s (ball 0 4) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ z ∈ ball (0:EuclideanSpace ℂ (Fin 3)) 4, (s z)^2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0:EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V*s z) →
    ∀ (f : Base → ℝ), (∀ x ∈ ball (0:Base) 4, F (DenseJet.realSlice x) = (f x:ℂ)) →
    ∀ (c s0 : ℝ) (L : Base →L[ℝ] ℝ),
      (∀ i j, HasRealExtension D' (fun x => hessian (fun y => (f y-c-L y)/s0) x i j)) ∧
      (∀ i j k, HasRealExtension D'
        (fun x => clearedCubicError (fun y => (f y-c-L y)/s0) x i j k)) := by
  refine ⟨8*(10000*(D+2))+2, ?_⟩
  intro Δ U V W hΔ hU hV hW hΔne hWne s F hs hF hroot hrep f hf c s0 L
  have hFrep : SqrtRep (ball 0 4) s D F := ⟨hF,U,V,W,hWne,hU,hV,hW,hrep⟩
  let AffP : MvPolynomial (Fin 3) ℂ :=
    C (c:ℂ) + ∑ i : Fin 3, C (L (EuclideanSpace.single i 1):ℂ)*X i
  have hAffdeg : AffP.totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) ((totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun i _ => (totalDegree_mul _ _).trans (by simp))))
  have hAffeval : ∀ z : EuclideanSpace ℂ (Fin 3),
      eval (fun i => z i) AffP = DenseJet.complexAffine c L z := by
    intro z
    simp [AffP, DenseJet.complexAffine]
  let G : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => (F z-eval (fun i => z i) AffP)/(s0:ℂ)
  have hG : SqrtRep (ball 0 4) s (D+1) G :=
    (hFrep.sub ((SqrtRep.poly AffP).mono hAffdeg)).div_const _
  have hGr : ∀ x ∈ ball (0:Base) 4,
      G (DenseJet.realSlice x) = (((f x-c-L x)/s0:ℝ):ℂ) := by
    intro x hx
    have haff := DenseJet.complexAffine_real c L x
    rw [← DenseJet.realSlice_apply] at haff
    simp only [G]
    rw [hf x hx, hAffeval, haff]
    push_cast
    ring
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hasRealExtension_graph_entries_of_sqrtRep (hΔ.trans (by omega)) hΔne hs hroot hG hGr

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
