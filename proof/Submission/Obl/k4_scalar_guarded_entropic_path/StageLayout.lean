import Mathlib

/-! Choose the finite depth mesh, information window length and tangent
scale in this order. The scale can shrink after every finite count is fixed. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

noncomputable section

structure StageLayout (k : ℕ) (R δ κ η : ℝ) where
  m : ℕ
  m_one : 1 ≤ m
  m_stage : (k : ℝ) + 1 ≤ m
  m_range : R + 1 ≤ m
  mesh : ℝ
  mesh_pos : 0 < mesh
  mesh_error : mesh ≤ δ / 100
  mesh_range : mesh ≤ R⁻¹ / 100
  mesh_one : mesh ≤ 1 / 100
  coarse : ℕ
  C : ℕ
  coarse_lt : coarse + 1 < C
  coarse_depth : (m : ℝ) + 2 ≤ ((coarse : ℝ) + 1) * mesh
  depth_gap : (m : ℝ) + 2 ≤ κ * ((C : ℝ) - ((coarse : ℝ) + 1)) * mesh
  covers_range : R + 1 ≤ (C : ℝ) * mesh
  L : ℕ
  L_pos : 0 < L
  entropy_fraction : 8 * (C : ℝ) * ((m : ℝ) + 4) / (L : ℝ) ≤ δ
  scale : ℝ
  scale_pos : 0 < scale
  scale_error : scale ≤ δ
  scale_one : scale ≤ 1
  total_small : ((L + C + 1 : ℕ) : ℝ) * scale * mesh < 1 / 4
  range_small : scale * ((m : ℝ) + R + 1) < 1 / 4
  angular_small : scale * ((m : ℝ) + R + 1) < η / 4

theorem exists_stageLayout (k : ℕ) {R δ κ η : ℝ}
    (hR : 1 < R) (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    Nonempty (StageLayout k R δ κ η) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((k : ℝ) + 1) (R + 1))
  have hmk : (k : ℝ) + 1 ≤ m := (le_max_left _ _).trans hm.le
  have hmR : R + 1 ≤ m := (le_max_right _ _).trans hm.le
  have hm1 : 1 ≤ m := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  let mesh := min (δ / 100) (min (R⁻¹ / 100) (1 / 100))
  have hR0 : 0 < R := by linarith
  have hmesh : 0 < mesh := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hmeshδ : mesh ≤ δ / 100 := min_le_left _ _
  have hmeshR : mesh ≤ R⁻¹ / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hmesh1 : mesh ≤ 1 / 100 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨c, hc⟩ := exists_nat_gt (((m : ℝ) + 2) / mesh)
  have hcdepth : (m : ℝ) + 2 ≤ ((c : ℝ) + 1) * mesh := by
    have hcm := (div_lt_iff₀ hmesh).mp hc
    nlinarith only [hcm, hmesh]
  obtain ⟨C, hC⟩ := exists_nat_gt
    (max (((c : ℝ) + 2) + ((m : ℝ) + 2) / (κ * mesh)) ((R + 1) / mesh))
  have hC₁ := (le_max_left _ _).trans_lt hC
  have hC₂ := (le_max_right _ _).trans_lt hC
  have hpositive : 0 < ((m : ℝ) + 2) / (κ * mesh) := by positivity
  have hcC : c + 1 < C := by
    exact_mod_cast (show (c : ℝ) + 1 < C by linarith)
  have hgap : (m : ℝ) + 2 ≤ κ * ((C : ℝ) - ((c : ℝ) + 1)) * mesh := by
    have hg : ((m : ℝ) + 2) / (κ * mesh) < (C : ℝ) - ((c : ℝ) + 1) := by linarith
    have hg' := (div_lt_iff₀ (mul_pos hκ hmesh)).mp hg
    nlinarith only [hg']
  have hcover : R + 1 ≤ (C : ℝ) * mesh := ((div_lt_iff₀ hmesh).mp hC₂).le
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (8 * (C : ℝ) * ((m : ℝ) + 4) / δ))
  have hL₁ := (le_max_left _ _).trans_lt hL
  have hL₂ := (le_max_right _ _).trans_lt hL
  have hLpos : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hentropy : 8 * (C : ℝ) * ((m : ℝ) + 4) / (L : ℝ) ≤ δ := by
    apply (div_le_iff₀ hLposR).mpr
    have ht := (div_lt_iff₀ hδ).mp hL₂
    nlinarith only [ht]
  let A : ℝ := ((L + C + 1 : ℕ) : ℝ) * mesh + (m : ℝ) + R + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let sc := min (δ / 2) (min (1 / 2) (min ((1 / 16 : ℝ) / A) ((η / 16) / A)))
  have hsc : 0 < sc := lt_min (by positivity)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hscδ : sc ≤ δ := (min_le_left _ _).trans (by linarith)
  have hsc1 : sc ≤ 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans (by norm_num)
  have hscA : sc * A ≤ 1 / 16 := (le_div_iff₀ hA).mp
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hscη : sc * A ≤ η / 16 := (le_div_iff₀ hA).mp
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have htotal : ((L + C + 1 : ℕ) : ℝ) * sc * mesh < 1 / 4 := by
    have hsmall : ((L + C + 1 : ℕ) : ℝ) * sc * mesh ≤ sc * A := by
      dsimp [A]
      nlinarith only [hsc, (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), hR0]
    linarith
  have hrange : sc * ((m : ℝ) + R + 1) ≤ sc * A := by
    apply mul_le_mul_of_nonneg_left _ hsc.le
    dsimp [A]
    have hterm : 0 ≤ ((L + C + 1 : ℕ) : ℝ) * mesh := by positivity
    linarith
  exact ⟨⟨m, hm1, hmk, hmR, mesh, hmesh, hmeshδ, hmeshR, hmesh1, c, C, hcC,
    hcdepth, hgap, hcover, L, hLpos, hentropy, sc, hsc, hscδ, hsc1, htotal,
    by linarith [hscA], by linarith [hscη]⟩⟩

namespace StageLayout

variable {k : ℕ} {R δ κ η : ℝ} (q : StageLayout k R δ κ η)

def targets : List ℝ :=
  List.ofFn (fun j : Fin (q.L + q.C) => ((j.val : ℝ) + 1) * (q.scale * q.mesh))

theorem targets_length : q.targets.length = q.L + q.C := by simp [targets]

theorem targets_pairwise : q.targets.Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  apply mul_lt_mul_of_pos_right _ (mul_pos q.scale_pos q.mesh_pos)
  exact_mod_cast (show i.val + 1 < j.val + 1 from Nat.add_lt_add_right hij 1)

theorem targets_small : ∀ r ∈ q.targets, r < (1 / 4 : ℝ) := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  have hj : ((j.val : ℝ) + 1) ≤ ((q.L + q.C + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val + 1 ≤ q.L + q.C + 1 by omega)
  have hbound := mul_le_mul_of_nonneg_right hj (mul_nonneg q.scale_pos.le q.mesh_pos.le)
  nlinarith only [hbound, q.total_small]

theorem targets_mem : ∀ r ∈ q.targets, r ∈ Set.Ioo (0 : ℝ) 1 := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨mul_pos (by positivity) (mul_pos q.scale_pos q.mesh_pos), ?_⟩
  have hj : ((j.val : ℝ) + 1) ≤ ((q.L + q.C + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val + 1 ≤ q.L + q.C + 1 by omega)
  have hbound := mul_le_mul_of_nonneg_right hj (mul_nonneg q.scale_pos.le q.mesh_pos.le)
  nlinarith only [hbound, q.total_small]

theorem targets_grid (j : Fin q.targets.length) :
    q.targets[j.val] = 0 + ((j.val : ℝ) + 1) * (q.scale * q.mesh) := by
  simp only [targets, List.getElem_ofFn, zero_add]

end StageLayout

end

end Submission.Obl.k4_scalar_guarded_entropic_path
