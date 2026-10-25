-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

/-- The square condition in the frozen statement. -/
def InUnitSquare (F : Set Plane) : Prop :=
  ∀ a ∈ F, ∀ i : Fin 2, 0 ≤ a i ∧ a i ≤ 1

/-- The one-dimensional Assouad cover bound in the frozen statement. -/
def AD (δ C : ℝ) (F : Set Plane) : Prop :=
  ∀ (x : Plane) (ρ r : ℝ), δ ≤ ρ → ρ ≤ r →
    ∃ (m : ℕ) (cc : Fin m → Plane),
      Covers ρ (F ∩ Metric.ball x r) cc ∧ (m : ℝ) ≤ C * (r / ρ)

def LineConclusion (δ ε : ℝ) (F G : Set Plane) : Prop :=
  ∃ (e b₀ : Plane) (c : ℝ), ‖e‖ = 1 ∧
    CoverLower δ (Metric.thickening δ {a | inner ℝ a e = c} ∩ F) (δ ^ (ε - 1)) ∧
    CoverLower δ (Metric.thickening δ (Set.range (fun t : ℝ => b₀ + t • e)) ∩ G)
      (δ ^ (ε - 1))

def DotSet (Q : Set Triple) : Set ℝ :=
  {t | ∃ h ∈ Q, t = inner ℝ h.1 (h.2.1 - h.2.2)}

def ProjectionGain (δ η ε : ℝ) (Q : Set Triple) : Prop :=
  ∃ ρ a L : ℝ, δ ≤ ρ ∧ δ ^ (-η) * ρ ≤ L ∧
    CoverLower ρ (Set.Icc a (a + L) ∩ DotSet Q) ((L / ρ) ^ (1 - ε))

def ProjectionConclusion (δ η ε : ℝ) (F G : Set Plane) : Prop :=
  ∀ Q : Set Triple, Q ⊆ F ×ˢ (G ×ˢ G) →
    CoverLower δ Q (δ ^ (η - 3)) → ProjectionGain δ η ε Q

theorem AD.mono_constant {δ C D : ℝ} {F : Set Plane} (h : AD δ C F)
    (hδ : 0 < δ) (hCD : C ≤ D) : AD δ D F := by
  intro x ρ r hδρ hρr
  obtain ⟨m, cc, hcov, hm⟩ := h x ρ r hδρ hρr
  refine ⟨m, cc, hcov, hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hCD (div_nonneg (hδ.le.trans (hδρ.trans hρr))
    (hδ.le.trans hδρ))

theorem AD.mono_eta {δ η θ : ℝ} {F : Set Plane} (h : AD δ (δ ^ (-θ)) F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθη : θ ≤ η) : AD δ (δ ^ (-η)) F :=
  h.mono_constant hδ (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hθη))

theorem LineConclusion.mono_epsilon {δ ε ε' : ℝ} {F G : Set Plane}
    (h : LineConclusion δ ε F G) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ ε') :
    LineConclusion δ ε' F G := by
  obtain ⟨e, b, c, he, hF, hG⟩ := h
  have hp : δ ^ (ε' - 1) ≤ δ ^ (ε - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (sub_le_sub_right hε 1)
  exact ⟨e, b, c, he, hF.weaken hp, hG.weaken hp⟩

theorem ProjectionGain.mono_epsilon {δ η ε ε' : ℝ} {Q : Set Triple}
    (h : ProjectionGain δ η ε Q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 ≤ η) (hε : ε ≤ ε') : ProjectionGain δ η ε' Q := by
  obtain ⟨ρ, a, L, hδρ, hL, hcov⟩ := h
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hpow : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hη)
  have hratio : 1 ≤ L / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  refine ⟨ρ, a, L, hδρ, hL, hcov.weaken ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hratio (sub_le_sub_left hε 1)

theorem ProjectionGain.mono_eta {δ η θ ε : ℝ} {Q : Set Triple}
    (h : ProjectionGain δ η ε Q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθη : θ ≤ η) : ProjectionGain δ θ ε Q := by
  obtain ⟨ρ, a, L, hδρ, hL, hcov⟩ := h
  refine ⟨ρ, a, L, hδρ, le_trans ?_ hL, hcov⟩
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hθη))
    (hδ.le.trans hδρ)

theorem ProjectionConclusion.mono_eta {δ η θ ε : ℝ} {F G : Set Plane}
    (h : ProjectionConclusion δ η ε F G) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθη : θ ≤ η) : ProjectionConclusion δ θ ε F G := by
  intro Q hQ hcov
  have hp : δ ^ (η - 3) ≤ δ ^ (θ - 3) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (sub_le_sub_right hθη 3)
  exact (h Q hQ (hcov.weaken hp)).mono_eta hδ hδ1 hθη

/-- For exponents at least one, any nonempty dot-product set gives the required gain. -/
theorem projectionGain_of_one_le_epsilon {δ η ε : ℝ} {Q : Set Triple}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hε : 1 ≤ ε) (hQ : Q.Nonempty) :
    ProjectionGain δ η ε Q := by
  obtain ⟨h, hh⟩ := hQ
  let a : ℝ := inner ℝ h.1 (h.2.1 - h.2.2)
  have hpow : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hη)
  refine ⟨δ, a, δ ^ (-η) * δ, le_rfl, le_rfl, coverLower_of_nonempty ?_ ?_⟩
  · refine ⟨a, ⟨⟨le_rfl, ?_⟩, h, hh, rfl⟩⟩
    have hp : 0 ≤ δ ^ (-η) * δ := mul_nonneg (by positivity) hδ.le
    linarith
  · rw [mul_div_cancel_right₀ _ hδ.ne']
    exact Real.rpow_le_one_of_one_le_of_nonpos hpow (sub_nonpos.mpr hε)

theorem projectionConclusion_of_one_le_epsilon {δ η ε : ℝ} {F G : Set Plane}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hε : 1 ≤ ε) :
    ProjectionConclusion δ η ε F G := by
  intro Q hQ hcov
  exact projectionGain_of_one_le_epsilon hδ hδ1 hη hε
    (hcov.nonempty (Real.rpow_pos_of_pos hδ _))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
