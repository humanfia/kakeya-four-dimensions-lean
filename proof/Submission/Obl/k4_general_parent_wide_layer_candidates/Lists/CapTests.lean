import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.FrameCaps
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Numerics

/-!
# The scalar cap tests of a native list frame

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation`, files
`Numerics.lean` and `CapTests.lean`). The only change in the mesh is that the
scalar mesh `N^(-m)` resolves the parent's transverse width `N^(-ℓ r)` by the list
exponent condition `ℓ * r ≤ m` instead of `ℓ = κ ≤ 1`.
-/

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- One fixed fine mesh resolving a frame and its motion. -/
structure FrameMesh {k : ℕ} {r v m ε : ℝ} (f : p.ListFrame k r v m ε) : Prop where
  fine_le_one : p.N k ^ (-(100 * m)) ≤ 1
  mesh_le_transverse : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r)
  cell : p.N k ^ (-(100 * m)) ≤ f.q * p.N k ^ (-m)
  transverse : p.N k ^ (-(100 * m)) ≤
    2 * p.K k * f.q * p.N k ^ (-p.ℓ * r)
  motion_cell : p.K k * (1 + p.N k ^ (m / 10)) * p.N k ^ (-(100 * m)) ≤
    f.q * p.N k ^ (-m)
  motion_transverse : p.K k * (1 + p.N k ^ (m / 10)) * p.N k ^ (-(100 * m)) ≤
    2 * p.K k * f.q * p.N k ^ (-p.ℓ * r)
  velocity : |f.zv| ≤ p.K k * (1 + p.N k ^ (m / 10))
  transverse_velocity : |p.c k r f.parent 3 + p.c k r f.parent 4 * f.zv| ≤
    p.K k * (1 + p.N k ^ (m / 10))
  background : 216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 *
    p.N k ^ (-(100 * m)) ≤ p.N k ^ (-(r + v))

/-- One fixed fine exponent works for every incoming frame, every scalar
signal test depth, and every later law restriction. -/
theorem Valid.eventually_frame_mesh (h : p.Valid)
    {r v m : ℝ} (hr : 0 < r) (hv : 0 < v) (hm : 100 * (r + v) < m)
    (hℓm : p.ℓ * r ≤ m) :
    ∀ᶠ k in atTop, ∀ ε : ℝ, ∀ f : p.ListFrame k r v m ε,
      ParentGeometry p k r → FrameMesh f := by
  have hm0 : 0 < m := by linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have h₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 1
    (show -(100 * m) + m / 5 < -m by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  have h₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 2
    (show -(100 * m) + m / 10 < -(r + v) by linarith) (show (0 : ℝ) ≤ 864 by norm_num)
  filter_upwards [h₁, h₂] with k h₁ h₂
  intro ε f a
  let H := p.N k ^ (m / 10)
  let δ := p.N k ^ (-(100 * m))
  let ξ := p.N k ^ (-m)
  let g := p.N k ^ (-p.ℓ * r)
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hH : 1 ≤ H := Real.one_le_rpow (hN1 k) (by positivity)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hpow₁ : H ^ 2 * δ = p.N k ^ (-(100 * m) + m / 5) := by
    dsimp [H, δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  have hpow₂ : H * δ = p.N k ^ (-(100 * m) + m / 10) := by
    dsimp [H, δ]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hsmall : 2 * p.K k * H ^ 2 * δ ≤ ξ := by
    rw [mul_assoc (2 * p.K k), hpow₁]
    simpa only [pow_one] using h₁.le
  have hξg : ξ ≤ g := by
    apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
    rw [neg_mul]
    linarith
  have bounds := Submission.Obl.k4_wide_velocity_lists_scalar_preparation.resolving_bounds
    f.q_pos hK hH hδ hξg f.frame_component_bounds.1 hsmall
  refine ⟨Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith), hξg,
    bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2, ?_, ?_, ?_⟩
  · have hz := f.frame_component_bounds.2
    have hKH : H ≤ p.K k * (1 + H) := by nlinarith
    exact hz.trans hKH
  · calc
      _ ≤ |p.c k r f.parent 3| + |p.c k r f.parent 4| * |f.zv| := by
        rw [← abs_mul]
        exact abs_add_le _ _
      _ ≤ p.K k + p.K k * H := by
        gcongr
        · exact a.coefficient_bound f.parent 3
        · exact a.coefficient_bound f.parent 4
        · exact f.frame_component_bounds.2
      _ = _ := by dsimp [H]; ring
  · have hh : 216 * H * (2 * p.K k) ^ 2 * δ =
        864 * p.K k ^ 2 * p.N k ^ (-(100 * m) + m / 10) := by
      rw [← hpow₂]
      ring
    change 216 * H * (2 * p.K k) ^ 2 * δ ≤ p.N k ^ (-(r + v))
    rw [hh]
    exact h₂.le

namespace ListFrame

variable {k : ℕ} {r v m ε vMin vMax : ℝ} (f : p.ListFrame k r v m ε)

private theorem inverse_hidden_power (hN : 0 < p.N k) :
    ((p.N k ^ (-r)) ^ p.d)⁻¹ = p.N k ^ (p.d * r) := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_neg hN.le]
  congr 1
  ring

/-- Every intermediate scalar signal-depth cap comes from the uniform
original native cap, with the exact density `N^(d*r)`. -/
theorem pure_cell_cap
    (h : p.Valid) (a : ParentGeometry p k r) (mesh : FrameMesh f)
    (caps : FineCaps p k (100 * m) (r + v) vMin vMax)
    (s : ℝ) (hs : 0 ≤ s) (hsv : s ≤ r + v) (β : Fin 2 → ℤ) (j : ℤ) :
    f.law {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (8400 * p.K k ^ 3 * p.N k ^ (p.d * r) *
        (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d) := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hbg := mesh.background.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (show -(r + v) ≤ -s by linarith))
  have hh := f.original_scalar_cell_cap h a
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
    mesh.fine_le_one mesh.mesh_le_transverse (by positivity)
    mesh.cell mesh.transverse mesh.motion_cell mesh.motion_transverse
    mesh.velocity mesh.transverse_velocity hbg (fun _ => True) (by simp) 1
    (by
      intro q j
      simp only [and_true, mul_one]
      exact caps.pure s hs hsv q j)
    β j
  rw [inverse_hidden_power (p := p) (r := r) hN] at hh
  simpa only [and_true, mul_one] using hh

/-- The same residual cap retains one unchanged original velocity atom. -/
theorem original_velocity_bin_cap
    (h : p.Valid) (a : ParentGeometry p k r) (mesh : FrameMesh f)
    (caps : FineCaps p k (100 * m) (r + v) vMin vMax)
    (s θ : ℝ) (hs : 0 ≤ s) (hsv : s ≤ r + v)
    (hθmin : vMin ≤ θ) (hθmax : θ ≤ vMax)
    (β : Fin 2 → ℤ) (j b : ℤ) :
    f.law {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j ∧
      ⌊p.b k ω.1 3 / p.N k ^ (-θ)⌋ = b} ≤
      ENNReal.ofReal (8400 * p.K k ^ 3 * p.N k ^ (p.d * r) *
        (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d) *
        p.π k {w | ⌊w / p.N k ^ (-θ)⌋ = b} := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hb := (h.basic k).1
  have hcond : MeasurableSet {ω : α × ℝ | ⌊p.b k ω.1 3 / p.N k ^ (-θ)⌋ = b} :=
    (Int.measurable_floor.comp
      ((((measurable_pi_apply 3).comp hb).comp measurable_fst).div_const _))
        (measurableSet_singleton b)
  have hbg := mesh.background.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (show -(r + v) ≤ -s by linarith))
  have hh := f.original_scalar_cell_cap h a
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
    mesh.fine_le_one mesh.mesh_le_transverse (by positivity)
    mesh.cell mesh.transverse mesh.motion_cell mesh.motion_transverse
    mesh.velocity mesh.transverse_velocity hbg
    (fun ω => ⌊p.b k ω.1 3 / p.N k ^ (-θ)⌋ = b) hcond
    (p.π k {w | ⌊w / p.N k ^ (-θ)⌋ = b})
    (by
      intro q j
      exact caps.joint s θ hs hsv hθmin hθmax q j b)
    β j
  rw [inverse_hidden_power (p := p) (r := r) hN] at hh
  exact hh

/-- Translating the original velocity by the frame velocity meets at most
five original bins. The original palette cap then supplies angular decay. -/
theorem translated_velocity_bin_cap
    (h : p.Valid) (a : ParentGeometry p k r) (mesh : FrameMesh f)
    (caps : FineCaps p k (100 * m) (r + v) vMin vMax)
    (s θ : ℝ) (hs : 0 ≤ s) (hsv : s ≤ r + v)
    (hθmin : vMin ≤ θ) (hθmax : θ ≤ vMax)
    (β : Fin 2 → ℤ) (j b : ℤ) :
    f.law {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j ∧
      ⌊f.coeff ω.1 1 / p.N k ^ (-θ)⌋ = b} ≤
      ENNReal.ofReal (42000 * p.K k ^ 4 * p.N k ^ (p.d * r) *
        (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d * p.N k ^ (-p.S * θ)) := by
  classical
  let χ := p.N k ^ (-θ)
  let center := f.zv + (b : ℝ) * χ
  let J : Finset ℤ := (Finset.Icc (-2 : ℤ) 2).image (fun c => ⌊center / χ⌋ + c)
  let target : Set (α × ℝ) := {ω | scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j ∧ ⌊f.coeff ω.1 1 / χ⌋ = b}
  let E := target ∩ {ω | ω.1 ∈ f.good}
  let cell (c : ℤ) : Set (α × ℝ) := {ω |
    scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)) = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-s)⌋ = j ∧ ⌊p.b k ω.1 3 / χ⌋ = c}
  let C := 8400 * p.K k ^ 4 * p.N k ^ (p.d * r) *
    (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d * p.N k ^ (-p.S * θ)
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hJ : J.card ≤ 5 := Finset.card_image_le.trans (by norm_num)
  have hsub : E ⊆ ⋃ c ∈ J, cell c := by
    intro ω hω
    have hv := f.velocity_eq ω.1 hω.2
    have hlo := (le_div_iff₀ hχ).mp (Int.floor_le (f.coeff ω.1 1 / χ))
    have hhi := (div_lt_iff₀ hχ).mp (Int.lt_floor_add_one (f.coeff ω.1 1 / χ))
    rw [hω.1.2.2] at hlo hhi
    have hfit : |p.b k ω.1 3 - center| ≤ 1 * χ := by
      dsimp [center]
      rw [abs_le]
      constructor <;> linarith
    have hoff := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem hχ hfit
    norm_num at hoff
    have hm : ⌊p.b k ω.1 3 / χ⌋ ∈ J := by
      apply Finset.mem_image.mpr
      refine ⟨⌊p.b k ω.1 3 / χ⌋ - ⌊center / χ⌋, ?_, by omega⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact mem_iUnion₂.mpr ⟨_, hm, hω.1.1, hω.1.2.1, rfl⟩
  have hcell (c : ℤ) : f.law (cell c) ≤ ENNReal.ofReal C := by
    have hc := f.original_velocity_bin_cap h a mesh caps s θ hs hsv hθmin hθmax β j c
    apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (8400 * p.K k ^ 3 * p.N k ^ (p.d * r) *
            (p.N k ^ (-m)) ^ 2 * (p.N k ^ (-s)) ^ p.d) *
            ENNReal.ofReal (p.K k * p.N k ^ (-p.S * θ)) :=
        mul_le_mul' le_rfl (caps.palette θ hθmin hθmax c)
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [C]
        ring
  change f.law target ≤ _
  rw [← measure_inter_conull (ae_iff.mp f.good_ae)]
  change f.law E ≤ _
  calc
    _ ≤ f.law (⋃ c ∈ J, cell c) := measure_mono hsub
    _ ≤ ∑ c ∈ J, f.law (cell c) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ J, ENNReal.ofReal C := Finset.sum_le_sum (fun c _ => hcell c)
    _ = (J.card : ℝ≥0∞) * ENNReal.ofReal C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (5 : ℝ≥0∞) * ENNReal.ofReal C := mul_le_mul' (by exact_mod_cast hJ) le_rfl
    _ = _ := by
      rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [C]
      ring

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
