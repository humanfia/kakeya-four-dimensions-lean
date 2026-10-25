-- Lane B: almost-everywhere statements for a pushed-forward event law, from pointwise ones.
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniCleared
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineTransport

/-!
# From events to almost every base point

The analytic restoration asks for its tests almost everywhere for the law of the base points of
the retained events, `(μ.restrict S).map X`. The tests are known at every `X e`, `e ∈ S`. A test
whose failures lie in a measurable set avoiding `X '' S` holds almost everywhere; for the cleared
cubic error this set is open in the ball by continuity, and for the seven Hessian tests it is
measurable after moving the directions to rational ones (a countable union), at the price of a
factor two in every bound.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Set MeasureTheory Metric FubiniHessian

/-- A property holds almost everywhere for the image law if its failures lie in a measurable set
that the image of the retained set avoids. -/
theorem ae_map_restrict_of_bad_set {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (S : Set α) (X : α → β) (hX : Measurable X) (P : β → Prop)
    (B : Set β) (hB : MeasurableSet B) (hPB : ∀ x, ¬ P x → x ∈ B) (hSB : ∀ e ∈ S, X e ∉ B) :
    ∀ᵐ x ∂(μ.restrict S).map X, P x := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => hPB x hx) ?_
  rw [Measure.map_apply hX hB, Measure.restrict_apply (hX hB)]
  have h : X ⁻¹' B ∩ S = ∅ := by
    ext e
    simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 => hSB e h2 h1
  rw [h, measure_empty]

/-- The cleared cubic error is continuous where `g` is `C⁶`: it is a polynomial in the second
and third jets. -/
private theorem continuousOn_clearedCubicError_aux {g : Base → ℝ} {U : Set Base}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 6 g U) (i j k : Fin 3) :
    ContinuousOn (fun x => clearedCubicError g x i j k) U := by
  have hjet : ∀ (n : ℕ) (a : Fin n → Fin 3), n ≤ 6 →
      ContinuousOn (FubiniJets.jet g n a) U := by
    intro n a hn
    refine (FubiniJets.contDiffOn_jet hU hg (M := 0) ?_ a).continuousOn
    rw [zero_add]
    exact_mod_cast hn
  have hH : ContinuousOn (fun x => hessian g x) U := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
    exact hjet 2 ![a, b] (by norm_num)
  have hT : ContinuousOn (fun x => cubic g x) U := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => continuousOn_pi.2 fun c => ?_
    exact hjet 3 ![a, b, c] (by norm_num)
  have hΦ : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × ConicTensor.Tensor =>
      ConicTensor.cleared p.1 p.2 i j k) := by
    unfold ConicTensor.cleared fubiniCubic
    fun_prop
  have h := hΦ.comp_continuousOn (hH.prodMk hT)
  exact h

/-- The cleared cubic error bound at every retained base point holds almost everywhere. -/
theorem ae_cleared_of_forall {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (X : α → Base) (hX : Measurable X) {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (ball 0 4))
    {ε : ℝ}
    (hgood : ∀ e ∈ S, X e ∈ ball (0 : Base) 4 ∧
      ∀ i j k, |clearedCubicError g (X e) i j k| ≤ ε) :
    ∀ᵐ x ∂(μ.restrict S).map X, ∀ i j k, |clearedCubicError g x i j k| ≤ ε := by
  -- the failures lie outside the ball or in an open subset of it
  let B : Set Base := (ball (0 : Base) 4)ᶜ ∪ ⋃ i : Fin 3, ⋃ j : Fin 3, ⋃ k : Fin 3,
    (ball (0 : Base) 4 ∩ (fun x => |clearedCubicError g x i j k|) ⁻¹' Ioi ε)
  have hB : MeasurableSet B := by
    refine measurableSet_ball.compl.union ?_
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion
      fun k => ?_
    exact ((continuousOn_clearedCubicError_aux isOpen_ball hg i j k).abs.isOpen_inter_preimage
      isOpen_ball isOpen_Ioi).measurableSet
  refine ae_map_restrict_of_bad_set μ S X hX _ B hB ?_ ?_
  · intro x hx
    by_cases hxU : x ∈ ball (0 : Base) 4
    · simp only [not_forall, not_le] at hx
      obtain ⟨i, j, k, hijk⟩ := hx
      exact Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨k, hxU, hijk⟩⟩⟩)
    · exact Or.inl hxU
  · intro e he hmem
    obtain ⟨hXe, hle⟩ := hgood e he
    rcases hmem with h | h
    · exact h hXe
    · simp only [mem_iUnion] at h
      obtain ⟨i, j, k, -, hlt⟩ := h
      exact absurd (hle i j k) (not_le.2 hlt)

/-- Directions with first coordinate one and rational remaining coordinates. -/
private def ratDirections (q : Fin 7 → Fin 3 → ℚ) : Fin 7 → Base :=
  fun i => WithLp.toLp 2 (fun k => if k = 0 then 1 else (q i k : ℝ))

private theorem ratDirections_zero (q : Fin 7 → Fin 3 → ℚ) (i : Fin 7) :
    ratDirections q i 0 = 1 := by
  simp [ratDirections]

/-- The determinant of three of seven directions depends continuously on the directions. -/
private theorem continuous_det_three (i j k : Fin 7) :
    Continuous (fun p : Fin 7 → Base =>
      Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)) := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro r t
  fin_cases r <;> simp <;> fun_prop

open Filter Topology in
/-- Directions satisfying the conditions with constants `A`, `η` can be replaced by rational
directions (first coordinate one) satisfying them with doubled constants: the doubled conditions
hold strictly at the given directions, hence near them, and rational points are dense. -/
private theorem exists_rat_directions
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Base) ℝ)
    {A η : ℝ} (hA : 0 < A) (hη : 0 < η) (p : Fin 7 → Base)
    (hp1 : ∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A)
    (hp2 : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|)
    (hp3 : ∀ i, |L (fun _ => p i)| ≤ η) :
    ∃ q : Fin 7 → Fin 3 → ℚ,
      (∀ i, ‖ratDirections q i‖ ≤ 2 * A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        (2 * A)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 =>
          (![ratDirections q i, ratDirections q j, ratDirections q k] r) t)|) ∧
      (∀ i, |L (fun _ => ratDirections q i)| ≤ 2 * η) := by
  classical
  -- real parameters of directions with first coordinate one
  let ψ : (Fin 7 → Fin 3 → ℝ) → (Fin 7 → Base) :=
    fun c i => WithLp.toLp 2 (fun k => if k = 0 then 1 else c i k)
  have hψ : Continuous ψ := by
    refine continuous_pi fun i => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      exact continuous_const
    · simp only [hk, ↓reduceIte]
      exact (continuous_apply k).comp (continuous_apply i)
  let c₀ : Fin 7 → Fin 3 → ℝ := fun i k => p i k
  have hc₀ : ψ c₀ = p := by
    funext i
    ext k
    by_cases hk : k = 0
    · subst hk
      simp [ψ, (hp1 i).1]
    · simp [ψ, c₀, hk]
  have ht : Tendsto ψ (𝓝 c₀) (𝓝 p) := hc₀ ▸ hψ.tendsto c₀
  have hAA : (2 * A)⁻¹ < A⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) hA]
    linarith
  have hev : ∀ᶠ c in 𝓝 c₀, (∀ i, ‖ψ c i‖ < 2 * A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        (2 * A)⁻¹ < |Matrix.det (Matrix.of fun r t : Fin 3 => (![ψ c i, ψ c j, ψ c k] r) t)|) ∧
      (∀ i, |L (fun _ => ψ c i)| < 2 * η) := by
    refine (eventually_all.2 fun i => ?_).and ((eventually_all.2 fun i => eventually_all.2
      fun j => eventually_all.2 fun k => ?_).and (eventually_all.2 fun i => ?_))
    · have hc : Continuous (fun p : Fin 7 → Base => ‖p i‖) := (continuous_apply i).norm
      have h1 := (hc.tendsto p).comp ht
      exact h1.eventually_lt_const (by linarith [(hp1 i).2])
    · simp only [eventually_imp_distrib_left]
      intro hij hik hjk
      have h1 := ((((continuous_det_three i j k).abs).tendsto p).comp ht)
      exact h1.eventually_const_lt (hAA.trans_le (hp2 i j k hij hik hjk))
    · have hc : Continuous (fun p : Fin 7 → Base => |L (fun _ => p i)|) :=
        (L.coe_continuous.comp (continuous_pi fun _ => continuous_apply i)).abs
      have h1 := (hc.tendsto p).comp ht
      exact h1.eventually_lt_const (by linarith [hp3 i])
  have hdense : DenseRange (fun q : Fin 7 → Fin 3 → ℚ => fun i k => (q i k : ℝ)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨c, ⟨q, rfl⟩, hc⟩ := hdense.inter_nhds_nonempty hev
  exact ⟨q, fun i => (hc.1 i).le, fun i j k hij hik hjk => (hc.2.1 i j k hij hik hjk).le,
    fun i => (hc.2.2 i).le⟩

/-- A relatively closed condition on an open set, for a function continuous there, cuts out a
measurable set. -/
private theorem measurableSet_inter_preimage_of_continuousOn {U : Set Base} (hU : IsOpen U)
    {F : Base → ℝ} (hF : ContinuousOn F U) {t : Set ℝ} (ht : IsClosed t) :
    MeasurableSet (U ∩ F ⁻¹' t) := by
  have hopen := hF.isOpen_inter_preimage hU ht.isOpen_compl
  have h : U ∩ F ⁻¹' t = U \ (U ∩ F ⁻¹' tᶜ) := by
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_preimage, mem_compl_iff, not_and, not_not]
    tauto
  rw [h]
  exact hU.measurableSet.diff hopen.measurableSet

/-- Seven conditioned Hessian tests at every retained base point hold almost everywhere, with
constants doubled. -/
theorem ae_directions_of_forall {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (X : α → Base) (hX : Measurable X) {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (ball 0 4))
    {A η : ℝ} (hA : 2 ≤ A) (hη : 0 < η)
    (hgood : ∀ e ∈ S, X e ∈ ball (0 : Base) 4 ∧ ∃ p : Fin 7 → Base,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
      (∀ i, |iteratedFDeriv ℝ 2 g (X e) (fun _ => p i)| ≤ η)) :
    ∀ᵐ x ∂(μ.restrict S).map X, ∃ p : Fin 7 → Base,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ 2 * A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        (2 * A)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
      (∀ i, |iteratedFDeriv ℝ 2 g x (fun _ => p i)| ≤ 2 * η) := by
  have hA0 : 0 < A := by linarith
  -- the conditions on rational directions that do not involve the base point
  let D : (Fin 7 → Fin 3 → ℚ) → Prop := fun q =>
    (∀ i, ‖ratDirections q i‖ ≤ 2 * A) ∧
    (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      (2 * A)⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 =>
        (![ratDirections q i, ratDirections q j, ratDirections q k] r) t)|)
  -- the good set: a countable union of relatively closed subsets of the ball
  let G : Set Base := ⋃ q : Fin 7 → Fin 3 → ℚ, {_x | D q} ∩ ⋂ i : Fin 7,
    (ball (0 : Base) 4 ∩
      (fun x => |iteratedFDeriv ℝ 2 g x (fun _ => ratDirections q i)|) ⁻¹' Iic (2 * η))
  have hcont : ∀ v : Base,
      ContinuousOn (fun x => |iteratedFDeriv ℝ 2 g x (fun _ => v)|) (ball (0 : Base) 4) := by
    intro v
    have h1 : ContinuousOn (iteratedFDeriv ℝ 2 g) (ball (0 : Base) 4) :=
      ContinuousOn.continuousOn_iteratedFDeriv hg isOpen_ball (by norm_num)
    exact (h1.eval_const (fun _ => v)).abs
  have hG : MeasurableSet G := by
    refine MeasurableSet.iUnion fun q => (MeasurableSet.const (D q)).inter ?_
    exact MeasurableSet.iInter fun i =>
      measurableSet_inter_preimage_of_continuousOn isOpen_ball (hcont _) isClosed_Iic
  refine ae_map_restrict_of_bad_set μ S X hX _ Gᶜ hG.compl ?_ ?_
  · intro x hx hxG
    apply hx
    simp only [G, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_preimage,
      mem_Iic] at hxG
    obtain ⟨q, hq, hx⟩ := hxG
    exact ⟨ratDirections q, fun i => ⟨ratDirections_zero q i, hq.1 i⟩, hq.2, fun i => (hx i).2⟩
  · intro e he hmem
    apply hmem
    obtain ⟨hXe, p, hp1, hp2, hp3⟩ := hgood e he
    obtain ⟨q, hq1, hq2, hq3⟩ :=
      exists_rat_directions (iteratedFDeriv ℝ 2 g (X e)) hA0 hη p hp1 hp2 hp3
    simp only [G, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_preimage, mem_Iic]
    exact ⟨q, ⟨hq1, hq2⟩, fun i => ⟨hXe, hq3 i⟩⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
