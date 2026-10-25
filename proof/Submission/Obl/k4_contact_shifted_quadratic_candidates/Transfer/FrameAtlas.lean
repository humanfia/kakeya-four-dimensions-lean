/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameAtlas.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameMasses

/-!
# The atlas body of the residual model at one grid level

At an index with a good frame, every grid level of the residual model satisfies
the horizontal atlas body with the constant `K₁ ≥ 20 K³ K₂ H / θ`, provided the
slope bounds of its labels' affine parts (proved separately by nested
calibration).
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The affine part of a residual label's test. -/
def Frame.labelL (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) : Fin 4 → ℝ :=
  f.resL (f.pal h (f.node h i).1 (lastEntry h (f.node h i).2))

/-- The slope bounds of the residual labels at one level. -/
def FrameSlopes (f : Frame D k s₀ U') (h : ℕ) (K₁ : ℝ) : Prop :=
  ∀ i : Fin (f.retained h).card,
    |f.labelL h i 3| ≤ K₁ * (1 + D.N k ^ (-((h : ℝ) * (U' / f.m))) /
        ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2) ∧
    ∀ l ∈ (f.level h).B i, ∀ t ∈ Data.I (f.level h).T ((f.level h).j i),
      |f.labelL h i 1 - point (f.coeff l) t 1 * f.labelL h i 3| +
        |f.labelL h i 2 + t * f.labelL h i 3| ≤
        K₁ * (1 + D.N k ^ (-((h : ℝ) * (U' / f.m))) / (2 : ℝ) ^ (-(f.resT h : ℤ)))

theorem Frame.node_injective (f : Frame D k s₀ U') (h : ℕ) :
    Function.Injective (f.node h) := by
  intro i i' heq
  have : (f.retained h).equivFin.symm i = (f.retained h).equivFin.symm i' := Subtype.ext heq
  exact (f.retained h).equivFin.symm.injective this

theorem FrameGood.res_disjoint (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i i' : Fin (f.level h).n) (hii' : i ≠ i')
    (hj : (f.level h).j i = (f.level h).j i') :
    Disjoint ((f.level h).A i) ((f.level h).A i') := by
  have hne : f.node h i ≠ f.node h i' := fun heq => hii' (f.node_injective h heq)
  by_cases h1 : (f.node h i).1 = (f.node h i').1
  · have h2 : (f.node h i).2 ≠ (f.node h i').2 := fun h2 => hne (Prod.ext h1 h2)
    change Disjoint (f.hist h (f.node h i).1 (f.node h i).2)
      (f.hist h (f.node h i').1 (f.node h i').2)
    rw [← h1]
    exact disjoint_historyAssignment _ _ _ _
      (fun h' i'' => disjoint_assignedAffineEntry _ _ _ _ _ _) h (f.node h i).1 h2
  · -- different original labels in the same original block
    have hv : (((f.level h).j i : ℕ)) = (((f.level h).j i' : ℕ)) := congrArg Fin.val hj
    rw [f.resj_val (hg.inside hh i).1, f.resj_val (hg.inside hh i').1] at hv
    have ho : (D.j k (f.depth 0) f.i₀ : ℕ) * 2 ^ f.resT h ≤
        (D.j k (f.depth h) (f.node h i).1 : ℕ) := (dyadic_offset (hg.inside hh i).1).1
    have ho' : (D.j k (f.depth 0) f.i₀ : ℕ) * 2 ^ f.resT h ≤
        (D.j k (f.depth h) (f.node h i').1 : ℕ) := (dyadic_offset (hg.inside hh i').1).1
    have hjj : D.j k (f.depth h) (f.node h i).1 = D.j k (f.depth h) (f.node h i').1 := by
      apply Fin.ext
      generalize (D.j k (f.depth 0) f.i₀ : ℕ) * 2 ^ f.resT h = c at hv ho ho'
      omega
    exact (hg.disj h hh _ _ h1 hjj).mono (f.hist_subset_A h _ _) (f.hist_subset_A h _ _)

/-- The horizontal atlas body of the residual model at a grid level. -/
theorem FrameGood.atlasBody (hg : FrameGood f Rk θ K₂ e₀') {K' : ℕ → ℝ}
    {fr : (k : ℕ) → Option (Frame D k s₀ U')} (hfr : fr k = some f)
    {h : ℕ} (hh : h ≤ f.m) {R K₁ : ℝ} (hR0 : 0 < R) (hR : R ≤ Rk)
    (hK₁ : 20 * D.K k ^ 3 * K₂ * f.H / θ ≤ K₁) (hslope : FrameSlopes f h K₁) :
    AtlasBody (residualData D s₀ U' e₀' K' fr) k R ((h : ℝ) * (U' / f.m)) (f.level h) K₁ := by
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hH : 1 ≤ f.H := hg.H_ge
  have hθ := hg.θ_pos
  have hθ1 := hg.θ_le
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  -- the base constant dominates every individual loss
  set B₀ := 20 * D.K k ^ 3 * K₂ * f.H / θ with hB₀
  have hK1 : 1 ≤ D.K k ^ 3 := one_le_pow₀ hK
  have hKsq : D.K k ^ 2 ≤ D.K k ^ 3 := pow_le_pow_right₀ hK (by norm_num)
  have hB : D.K k ^ 3 * K₂ * f.H ≤ B₀ * θ := by
    rw [hB₀, div_mul_cancel₀ _ hθ.ne']
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ D.K k ^ 3) (by linarith : (0:ℝ) ≤ K₂))
      (by linarith : (0:ℝ) ≤ f.H)]
  have hB1 : D.K k ^ 3 * K₂ * f.H ≤ B₀ := by
    have : B₀ * θ ≤ B₀ := mul_le_of_le_one_right (by
      rw [hB₀]; positivity) hθ1
    linarith
  have hKH : D.K k ^ 3 ≤ D.K k ^ 3 * K₂ * f.H := by
    have : 1 ≤ K₂ * f.H := one_le_mul_of_one_le_of_one_le hK₂ hH
    nlinarith
  have hK₂H : K₂ ≤ D.K k ^ 3 * K₂ * f.H := by
    have h1 : 1 ≤ D.K k ^ 3 * f.H := one_le_mul_of_one_le_of_one_le hK1 hH
    calc K₂ ≤ K₂ * (D.K k ^ 3 * f.H) := le_mul_of_one_le_right (by linarith) h1
      _ = _ := by ring
  have hHH : f.H ≤ D.K k ^ 3 * K₂ * f.H := by
    have h1 : 1 ≤ D.K k ^ 3 * K₂ := one_le_mul_of_one_le_of_one_le hK1 hK₂
    calc f.H ≤ f.H * (D.K k ^ 3 * K₂) := le_mul_of_one_le_right (by linarith) h1
      _ = _ := by ring
  have c1 : D.K k ^ 2 ≤ K₁ := by linarith
  have c3θ : D.K k ^ 3 / θ ≤ K₁ := by
    rw [div_le_iff₀ hθ]; nlinarith
  have c2 : D.K k ^ 2 / θ ≤ K₁ := (div_le_div_of_nonneg_right hKsq hθ.le).trans c3θ
  have cθ : θ⁻¹ ≤ K₁ := by
    rw [inv_eq_one_div]; exact (div_le_div_of_nonneg_right hK1 hθ.le).trans c3θ
  have h20 : 20 * (D.K k ^ 3 * K₂ * f.H) ≤ B₀ := by
    rw [hB₀, le_div_iff₀ hθ]
    have hp : 0 ≤ 20 * (D.K k ^ 3 * K₂ * f.H) := by
      have : 0 ≤ D.K k ^ 3 * K₂ * f.H := by
        have := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ D.K k ^ 3)
          (by linarith : (0:ℝ) ≤ K₂)) (by linarith : (0:ℝ) ≤ f.H)
        exact this
      linarith
    calc 20 * (D.K k ^ 3 * K₂ * f.H) * θ ≤ 20 * (D.K k ^ 3 * K₂ * f.H) * 1 :=
          mul_le_mul_of_nonneg_left hθ1 hp
      _ = 20 * D.K k ^ 3 * K₂ * f.H := by ring
  have hK2K : D.K k ^ 2 * K₂ ≤ D.K k ^ 3 * K₂ * f.H := by
    calc D.K k ^ 2 * K₂ ≤ D.K k ^ 3 * K₂ := mul_le_mul_of_nonneg_right hKsq (by linarith)
      _ ≤ D.K k ^ 3 * K₂ * f.H := le_mul_of_one_le_right (by positivity) hH
  have c5 : 20 * D.K k ^ 2 * K₂ ≤ K₁ := by linarith
  have c6 : f.H ≤ K₁ := by linarith
  have c7 : K₂ ≤ K₁ := by linarith
  have c8 : 1 ≤ K₁ := by linarith
  have hK₁0 : 0 < K₁ := by linarith
  have hμ := residual_μ (D := D) (s₀ := s₀) (U' := U') (e₀' := e₀') (K' := K') hfr
  have hν := residual_ν (D := D) (s₀ := s₀) (U' := U') (e₀' := e₀') (K' := K') hfr
  have hb := residual_b (D := D) (s₀ := s₀) (U' := U') (e₀' := e₀') (K' := K') hfr
  unfold AtlasBody
  simp only [hμ, hν, hb, residual_N, residual_κ, residual_ℓ, residual_d, residual_e₀,
    residual_π, residual_P, Data.x]
  have hcount := hg.res_count hh
  have hKpos : 0 < D.K k ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, fun i => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- lower block count
    refine le_trans ?_ hcount.1
    exact div_le_div_of_nonneg_left (by positivity) hKpos c1
  · -- upper block count
    refine hcount.2.trans ?_
    exact mul_le_mul_of_nonneg_right c1 (by positivity)
  · intro i
    exact ⟨hg.measurableSet_hist hh _ _, hg.measurableSet_hist hh _ _, subset_rfl⟩
  · intro i i' hii' hj
    exact hg.res_disjoint hh i i' hii' hj
  · -- floor
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hg.res_floor hh i)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) c3θ
  · -- ceiling
    refine (hg.res_ceil hh i).trans (ENNReal.ofReal_le_ofReal ?_)
    set A := (D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d
    set B := ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2
    set C := D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))
    have hX : 0 ≤ A * B * C := by positivity
    calc D.K k ^ 3 / θ * A * B * C = D.K k ^ 3 / θ * (A * B * C) := by ring
      _ ≤ K₁ * (A * B * C) := mul_le_mul_of_nonneg_right c3θ hX
      _ = K₁ * A * B * C := by ring
  · -- mass
    refine le_trans ?_ (hg.res_mass hh i)
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by positivity) (inv_pos.mpr hθ) cθ)) _
  · -- row constants
    intro e
    exact (hg.res_cbound hh i e).trans c5
  · exact resTest_degree _
  · -- rows
    intro l hl t ht
    obtain ⟨r1, r2, r3⟩ := hg.res_rows hh i l hl t ht
    refine ⟨r1.trans ?_, r2.trans ?_, r3.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right c1 (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c1 (by positivity))
        (by positivity)
    · exact mul_le_mul_of_nonneg_right c1 (by positivity)
  · -- fit
    intro l hl t ht
    rw [residual_x hfr]
    obtain ⟨f1, f2, f3⟩ := hg.res_fit hh i l hl t ht
    refine ⟨f1.trans (mul_le_mul_of_nonneg_right c6 (by positivity)), ?_, ?_⟩
    · rw [f2]; simpa using c8
    · rw [f3]; simp; positivity
  · -- hidden derivative floor
    filter_upwards with p _ _
    rw [show (f.level h).F i = X 3 - affineBase (f.labelL h i) from rfl, pderiv_resTest]
    simp only [map_one, abs_one]
    exact inv_le_one_of_one_le₀ c8
  · -- horizontal structure
    intro _
    refine ⟨trivial, hg.res_contact, (hg.res_centered hh i).trans
      (mul_le_mul_of_nonneg_right c7 (by positivity)), f.labelL h i, rfl, ?_⟩
    exact hslope i
  · -- coverage
    exact hg.res_cover hh
  · -- joint palette cap
    intro i v v₀ hv1 hv2
    have hRk : Rk⁻¹ ≤ v := (inv_anti₀ hR0 hR).trans hv1
    refine (hg.res_joint hh i v v₀ hRk (hv2.trans hR)).trans ?_
    exact mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right c2 (by positivity))) _) _

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
