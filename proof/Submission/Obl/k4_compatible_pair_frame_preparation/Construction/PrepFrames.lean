-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepFrames.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepFrames.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.FramePackage
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepTransport

/-!
# Fitting matrices of a scale class

The common frames of `FramePackage` (x0661) are fitted to the old chart matrices of one
scale class `R₁ ≤ r₁ < 2 R₁`, `R₂ ≤ r₂ < 2 R₂`.  In an *anisotropic* class the old
matrices are used as they are.  In an *isotropic* class (where the narrow scale is
not much smaller than the long one) the old matrix is replaced by `R₁ • 1`: every chart
of the class then has the same unit normal, so no pair of charts has separated normals,
and the old confinement survives with the constant `4 κ₀`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix Submission.Lib.K4VelocityStrips

/-- The frame-fitting matrix of an old chart of a class. -/
noncomputable def fitMat (iso : Prop) [Decidable iso] (R₁ : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if iso then R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) else Q

theorem det_smul_one_two (R₁ : ℝ) : (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = R₁ ^ 2 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

theorem col0_smul_one (R₁ : ℝ) : col0 (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
    WithLp.toLp 2 ![R₁, 0] := by
  ext i; fin_cases i <;> simp [col0]

theorem col1_smul_one (R₁ : ℝ) : col1 (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
    WithLp.toLp 2 ![0, R₁] := by
  ext i; fin_cases i <;> simp [col1]

theorem norm_toLp_two (a b : ℝ) : ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ =
    Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, sq_abs]

theorem r₁_smul_one {R₁ : ℝ} (hR : 0 < R₁) : r₁ (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = R₁ := by
  have h0 : ‖col0 (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ))‖ = R₁ := by
    rw [col0_smul_one, norm_toLp_two]
    simp [Real.sqrt_sq hR.le]
  have h1 : ‖col1 (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ))‖ = R₁ := by
    rw [col1_smul_one, norm_toLp_two]
    simp [Real.sqrt_sq hR.le]
  unfold r₁ longCol
  rw [ite_cond_eq_true _ _ (eq_true (by rw [h0, h1]))]
  exact h0

theorem r₂_smul_one {R₁ : ℝ} (hR : 0 < R₁) : r₂ (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = R₁ := by
  unfold r₂
  rw [r₁_smul_one hR, det_smul_one_two, abs_of_pos (by positivity)]
  field_simp

theorem inv_smul_one_two {R₁ : ℝ} (hR : R₁ ≠ 0) :
    (R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = R₁⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hR, one_mul, one_smul]

theorem entrySum_smul_one {R₁ : ℝ} (hR : 0 ≤ R₁) :
    (∑ i : Fin 2, ∑ j : Fin 2, |(R₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j|) = 2 * R₁ := by
  simp [Fin.sum_univ_two, Matrix.one_apply, abs_of_nonneg hR]
  ring

theorem stripWedge_self (n : EuclideanSpace ℝ (Fin 2)) : stripWedge n n = 0 := by
  unfold stripWedge; ring

/-- The properties of the fitting matrix of a chart in its class. -/
theorem fitMat_class (iso : Prop) [Decidable iso] {R₁ R₂ κ₀ : ℝ} {T₀ : ℕ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (hR₁ : 0 < R₁)
    (h1 : R₁ ≤ r₁ Q) (h1' : r₁ Q < 2 * R₁) (h2 : R₂ ≤ r₂ Q) (h2' : r₂ Q < 2 * R₂)
    (hR21 : R₂ ≤ R₁) (hsum : (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ κ₀ / 2 ^ T₀) :
    (fitMat iso R₁ Q).det ≠ 0 ∧ R₁ ≤ r₁ (fitMat iso R₁ Q) ∧ r₁ (fitMat iso R₁ Q) ≤ 2 * R₁ ∧
      r₂ (fitMat iso R₁ Q) ≤ 2 * (if iso then R₁ else R₂) ∧ (if iso then R₁ else R₂) ≤ R₁ ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |fitMat iso R₁ Q i j|) ≤ (4 * κ₀) / 2 ^ T₀ := by
  have hsum0 : 0 ≤ κ₀ / 2 ^ T₀ := le_trans (by positivity) hsum
  have hr1 := (r₁_le_entrySum Q).trans hsum
  unfold fitMat
  split_ifs with hiso
  · refine ⟨?_, ?_, ?_, ?_, le_rfl, ?_⟩
    · rw [det_smul_one_two]; positivity
    · rw [r₁_smul_one hR₁]
    · rw [r₁_smul_one hR₁]; linarith
    · rw [r₂_smul_one hR₁]; linarith
    · rw [entrySum_smul_one hR₁.le]
      have : (4 * κ₀) / 2 ^ T₀ = 4 * (κ₀ / 2 ^ T₀) := by ring
      rw [this]
      linarith
  · refine ⟨hQ, h1, h1'.le, h2'.le, hR21, hsum.trans ?_⟩
    have hp : (0 : ℝ) < 2 ^ T₀ := by positivity
    have hκ0 : 0 ≤ κ₀ := by
      have := mul_nonneg hsum0 hp.le
      rwa [div_mul_cancel₀ _ hp.ne'] at this
    gcongr
    linarith

theorem toEuclideanLin_smul_one (a : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin (a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) w = a • w := by
  ext i
  fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply]

/-- Old confinement in the fitting matrix, with the constant `4 κ₀`. -/
theorem fitMat_confined (iso : Prop) [Decidable iso] {R₁ κ₀ : ℝ} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) (hR₁ : 0 < R₁) (h1' : r₁ Q < 2 * R₁) (hκ₀ : 0 ≤ κ₀)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖Matrix.toEuclideanLin Q⁻¹ w‖ ≤ κ₀) :
    ‖Matrix.toEuclideanLin (fitMat iso R₁ Q)⁻¹ w‖ ≤ 4 * κ₀ := by
  unfold fitMat
  split_ifs
  · rw [inv_smul_one_two hR₁.ne', toEuclideanLin_smul_one, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hR₁]
    have hcancel := toEuclideanLin_inv_cancel hQ w
    have hle := norm_toEuclideanLin_le Q (Matrix.toEuclideanLin Q⁻¹ w)
    rw [hcancel] at hle
    have hr1 := r₁_nonneg Q
    rw [inv_mul_le_iff₀ hR₁]
    calc ‖w‖ ≤ 2 * ‖Matrix.toEuclideanLin Q⁻¹ w‖ * r₁ Q := hle
      _ ≤ 2 * κ₀ * (2 * R₁) := by
          apply mul_le_mul (by linarith) h1'.le hr1 (by positivity)
      _ = R₁ * (4 * κ₀) := by ring
  · linarith

/-- In an isotropic class all fitting matrices coincide. -/
theorem fitMat_iso_eq {iso : Prop} [Decidable iso] (hiso : iso) (R₁ : ℝ)
    (Q Q' : Matrix (Fin 2) (Fin 2) ℝ) : fitMat iso R₁ Q = fitMat iso R₁ Q' := by
  simp only [fitMat, hiso, ↓reduceIte]

theorem fitMat_aniso_eq {iso : Prop} [Decidable iso] (hiso : ¬ iso) (R₁ : ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : fitMat iso R₁ Q = Q := by
  simp only [fitMat, hiso, ↓reduceIte]

/-- The narrow class scale used for the frames: `R₁` in an isotropic class. -/
noncomputable def fitR₂ (iso : Prop) [Decidable iso] (R₁ R₂ : ℝ) : ℝ := if iso then R₁ else R₂

theorem fitR₂_pos (iso : Prop) [Decidable iso] {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) :
    0 < fitR₂ iso R₁ R₂ := by
  unfold fitR₂; split_ifs <;> assumption

theorem fitR₂_le (iso : Prop) [Decidable iso] {R₁ R₂ : ℝ} (hR21 : R₂ ≤ R₁) :
    fitR₂ iso R₁ R₂ ≤ R₁ := by
  unfold fitR₂; split_ifs <;> linarith

/-- The fitted scales of a chart of the class. -/
theorem fitMat_scales (iso : Prop) [Decidable iso] {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (h1' : r₁ Q < 2 * R₁)
    (h2' : r₂ Q < 2 * R₂) :
    (fitMat iso R₁ Q).det ≠ 0 ∧ r₁ (fitMat iso R₁ Q) ≤ 2 * R₁ ∧
      r₂ (fitMat iso R₁ Q) ≤ 2 * fitR₂ iso R₁ R₂ := by
  unfold fitMat fitR₂
  split_ifs
  · refine ⟨by rw [det_smul_one_two]; positivity, by rw [r₁_smul_one hR₁]; linarith,
      by rw [r₂_smul_one hR₁]; linarith⟩
  · exact ⟨hQ, h1'.le, h2'.le⟩

/-- **Witness lists or separated normals.**  For two old charts of a class sharing a
confined trajectory, world and coarse block, the source's frame key is listed by the
witness, unless the class is anisotropic and the old normals are separated by more
than `g`. -/
theorem srcKey_mem_or_separated {W C₀ T s : ℕ} (γ₀ : Fin C₀ → Fin W)
    (j₀ : Fin C₀ → Fin (2 ^ (T + s))) (c₀ u₀ : Fin C₀ → EuclideanSpace ℝ (Fin 2))
    (Q₀ : Fin C₀ → Matrix (Fin 2) (Fin 2) ℝ) (iso : Prop) [Decidable iso] {R₁ R₂ g κ₀ : ℝ}
    (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hR21 : R₂ ≤ R₁)
    (hκ₀ : 0 ≤ κ₀) {b b' : Fin C₀}
    (hQb : (Q₀ b).det ≠ 0) (hb1 : R₁ ≤ r₁ (Q₀ b)) (hb1' : r₁ (Q₀ b) < 2 * R₁)
    (hb2' : r₂ (Q₀ b) < 2 * R₂)
    (hQc : (Q₀ b').det ≠ 0) (hc1 : R₁ ≤ r₁ (Q₀ b')) (hc1' : r₁ (Q₀ b') < 2 * R₁)
    (hc2' : r₂ (Q₀ b') < 2 * R₂)
    (hγ : γ₀ b = γ₀ b') (hJ : coarseIdx (j₀ b) = coarseIdx (j₀ b')) {l : ℕ × (Fin 6 → ℝ)}
    (hl : OldConfined (j₀ b) (c₀ b) (u₀ b) (Q₀ b) κ₀ l)
    (hl' : OldConfined (j₀ b') (c₀ b') (u₀ b') (Q₀ b') κ₀ l)
    {Kb : ℕ} (hKb : 2 * (78 * (4 * κ₀)) + 1 ≤ (Kb : ℝ)) :
    srcKey γ₀ j₀ c₀ u₀ (fun b₁ => fitMat iso R₁ (Q₀ b₁)) g (2 ^ s * R₁)
        (2 ^ s * max (fitR₂ iso R₁ R₂) (g * R₁)) b ∈
      compatKeys γ₀ j₀ c₀ u₀ (fun b₁ => fitMat iso R₁ (Q₀ b₁)) g (2 ^ s * R₁)
        (2 ^ s * max (fitR₂ iso R₁ R₂) (g * R₁)) Kb b' ∨
    (¬ iso ∧ g < |stripWedge (nrm (Q₀ b)) (nrm (Q₀ b'))|) := by
  obtain ⟨fQb, f1b, f2b⟩ := fitMat_scales iso hR₁ hQb hb1' hb2'
  obtain ⟨fQc, f1c, f2c⟩ := fitMat_scales iso hR₁ hQc hc1' hc2'
  have fr1 (Q : Matrix (Fin 2) (Fin 2) ℝ) (h1 : R₁ ≤ r₁ Q) : R₁ ≤ r₁ (fitMat iso R₁ Q) := by
    unfold fitMat
    split_ifs
    · rw [r₁_smul_one hR₁]
    · exact h1
  have conf (b₁ : Fin C₀) (hQ : (Q₀ b₁).det ≠ 0) (h1' : r₁ (Q₀ b₁) < 2 * R₁)
      (hl₁ : OldConfined (j₀ b₁) (c₀ b₁) (u₀ b₁) (Q₀ b₁) κ₀ l) :
      OldConfined (j₀ b₁) (c₀ b₁) (u₀ b₁) (fitMat iso R₁ (Q₀ b₁)) (4 * κ₀) l := by
    intro t ht
    exact fitMat_confined iso hQ hR₁ h1' hκ₀ (hl₁ t ht)
  by_cases hw : |stripWedge (nrm (fitMat iso R₁ (Q₀ b))) (nrm (fitMat iso R₁ (Q₀ b')))| ≤ g
  · left
    exact srcKey_mem_compatKeys (γ₀ := γ₀) (j₀ := j₀) (c₀ := c₀) (u₀ := u₀)
      (Q₀ := fun b₁ => fitMat iso R₁ (Q₀ b₁)) hg hg8 hR₁ (fitR₂_pos iso hR₁ hR₂) (by linarith)
      hγ hJ fQb fQc f1b f2b f1c f2c (conf b hQb hb1' hl) (conf b' hQc hc1' hl') hw hKb
  · right
    by_cases hiso : iso
    · exfalso
      apply hw
      rw [fitMat_iso_eq hiso R₁ (Q₀ b) (Q₀ b'), stripWedge_self, abs_zero]
      exact hg.le
    · refine ⟨hiso, ?_⟩
      rw [fitMat_aniso_eq hiso, fitMat_aniso_eq hiso] at hw
      exact lt_of_not_ge hw

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
