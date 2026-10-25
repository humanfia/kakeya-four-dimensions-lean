-- Adapted from this LOT tree, o173, session x0581, commit b15c2c4d,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupCoords.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Compatibility

/-!
# Group coordinates on the observation space

For an old chart `(T, j₀, c, u, Q)`, a sub-box centre `v₀` and a radius `r > 0`, `groupBase` reads a
terminal observation as the point `r⁻¹ (u_obs - v₀)` of the group's comparison ball, where
`u_obs = (2^T t - j₀, z_obs)` is the normalized observed base point. For an incidence,
`u_obs = normBase` of its line (`normBaseObs_obs`), so `normBase = v₀ + r · groupBase`
(`normBase_eq_center_add`), and covered incidences of a box lie in the half ball when
`(κ + 2) 2^{-s₀} ≤ r / 2` (`groupBase_mem_halfBall`). The hidden coordinate `B w` lies in the
terminal bin of the observation (`hidden_mem_bin`).
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Submission.Lib.K4XInterface

/-- The normalized observed base point. -/
noncomputable def normBaseObs (T j₀ : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 ^ T * o.1 0 - j₀, (zcObs Q c u o) 0, (zcObs Q c u o) 1]

theorem normBaseObs_obs (T j₀ : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (Bv a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    normBaseObs T j₀ c u Q (obs Bv a p) = normBase T j₀ c u Q p.1 p.2 := by
  unfold normBaseObs normBase
  rw [zcObs_obs]
  rfl

theorem continuous_normBaseObs (T j₀ : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (normBaseObs T j₀ c u Q) := by
  unfold normBaseObs
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun e => ?_
  have ht : Continuous fun o : EuclideanSpace ℝ (Fin 3) × ℤ => o.1 0 :=
    (continuous_apply (0 : Fin 3)).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
  have hz := continuous_zcObs Q c u
  fin_cases e
  · exact (continuous_const.mul ht).sub continuous_const
  · exact (continuous_apply (0 : Fin 2)).comp ((PiLp.continuous_ofLp 2 _).comp hz)
  · exact (continuous_apply (1 : Fin 2)).comp ((PiLp.continuous_ofLp 2 _).comp hz)

/-- The group's comparison-ball coordinate of an observation. -/
noncomputable def groupBase (T j₀ : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (v₀ : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) : EuclideanSpace ℝ (Fin 3) :=
  r⁻¹ • (normBaseObs T j₀ c u Q o - v₀)

theorem measurable_groupBase (T j₀ : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (v₀ : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    Measurable (groupBase T j₀ c u Q v₀ r) := by
  unfold groupBase
  exact ((continuous_const (y := r⁻¹)).smul
    ((continuous_normBaseObs T j₀ c u Q).sub continuous_const)).measurable

theorem normBase_eq_center_add {T j₀ : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {v₀ : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : r ≠ 0)
    (Bv a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    normBase T j₀ c u Q p.1 p.2 = v₀ + r • groupBase T j₀ c u Q v₀ r (obs Bv a p) := by
  unfold groupBase
  rw [normBaseObs_obs, smul_smul, mul_inv_cancel₀ hr, one_smul]
  abel

/-- Covered incidences of a box lie in the half ball of the group coordinates. -/
theorem groupBase_mem_halfBall {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j₀ : ℕ} {rold Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T (j₀ : ℝ) rold Bv Ev c u Q R A F ex) {s₀ jj : ℕ} {k : Fin 2 → ℤ}
    {r : ℝ} (hr : 0 < r) (hside : side s₀ * (κ + 2) ≤ r / 2)
    {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hl : p.1 ∈ A)
    (hbox : inBox s₀ k (zc Q c u p.1 (subMid T s₀ j₀ jj)))
    (ht : p.2 ∈ Set.Icc ((subIdx s₀ j₀ jj : ℝ) / (2 : ℝ) ^ (T + s₀))
        (((subIdx s₀ j₀ jj : ℝ) + 1) / (2 : ℝ) ^ (T + s₀))) (Bv' a : ℝ) :
    ‖groupBase T j₀ c u Q (subBoxCenter s₀ jj k) r (obs Bv' a p)‖ ≤ 1 / 2 := by
  unfold groupBase
  rw [normBaseObs_obs, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hn := normBase_near_center h hl hbox ht
  calc r⁻¹ * ‖normBase T j₀ c u Q p.1 p.2 - subBoxCenter s₀ jj k‖ ≤ r⁻¹ * (r / 2) :=
        mul_le_mul_of_nonneg_left (hn.trans hside) (inv_nonneg.mpr hr.le)
    _ = 1 / 2 := by field_simp

/-- The hidden coordinate `B w` lies in the terminal bin of the observation. -/
theorem hidden_mem_bin {Bv a : ℝ} (ha : 0 < a) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    a * ((obs Bv a p).2 : ℝ) ≤ Bv * gx p.1 p.2 3 ∧
      Bv * gx p.1 p.2 3 ≤ a * (((obs Bv a p).2 : ℝ) + 1) := by
  change a * (⌊Bv * gx p.1 p.2 3 / a⌋ : ℝ) ≤ Bv * gx p.1 p.2 3 ∧
    Bv * gx p.1 p.2 3 ≤ a * ((⌊Bv * gx p.1 p.2 3 / a⌋ : ℝ) + 1)
  have h1 := Int.floor_le (Bv * gx p.1 p.2 3 / a)
  have h2 := Int.lt_floor_add_one (Bv * gx p.1 p.2 3 / a)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 ha.le
    rwa [mul_div_cancel₀ _ ha.ne'] at this
  · have := mul_le_mul_of_nonneg_left h2.le ha.le
    rwa [mul_div_cancel₀ _ ha.ne'] at this

end Submission.Obl.k4_clean_cover_graph_atlas
