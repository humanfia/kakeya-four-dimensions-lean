/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, JointScales.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeJointCap
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

open Filter MeasureTheory Set
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The frozen all-exponent native cap supplies the original fine cells at
any one fixed positive base and velocity exponent. -/
theorem Valid.eventually_native_fine_joint_cap (h : cfg.Valid)
    (s r a : ℝ) (hs : 0 ≤ s) (hr : 0 < r) (ha : 0 < a) :
    ∀ᶠ k in atTop, cfg.NativeFineJointCap k s (cfg.N k ^ (-r)) (cfg.N k ^ (-a)) := by
  let R := 2 + r + s + a + r⁻¹ + a⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hRpos : 0 < R := by linarith
  have hrR : r ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hsR : s ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have haR : a ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr ha]
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ hRpos hr).mpr
    dsimp [R]
    linarith [inv_pos.mpr ha]
  have hRa : R⁻¹ ≤ a := by
    apply (inv_le_comm₀ hRpos ha).mpr
    dsimp [R]
    linarith [inv_pos.mpr hr]
  filter_upwards [h.caps R hR] with k hk
  intro q b j
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hscale : cfg.N k ^ (-3 * r - cfg.d * s) =
      (cfg.N k ^ (-r)) ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    ring
  have hh := (hk r s a hRr hrR hs hsR hRa haR).2.2 false q b j
  rw [hscale] at hh
  have hzeq : cfg.z k (cfg.N k) r = fun (p : α × ℝ) (e : Fin 3) =>
      ⌊(![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3,
        cfg.b k p.1 1 + p.2 * cfg.b k p.1 4] : Fin 3 → ℝ) e / (cfg.N k ^ (-r))⌋ := by
    rfl
  rw [hzeq] at hh
  simpa [Data.x, mul_assoc] using hh

/-- Conditions needed to sum one finer original mesh over a normalized
Row cell and its original transverse range. -/
def JointMeshConditions (cfg : Data α) (k : ℕ) (s r a : ℝ) : Prop :=
  cfg.N k ^ (-r) ≤ cfg.timeLength k s * cfg.N k ^ (-a) ∧
    cfg.N k ^ (-r) ≤ cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) ∧
    3 * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s)

/-- A fixed sufficiently fine original mesh pays for every true label and
all subsequent restrictions of the residual. -/
theorem Valid.eventually_native_joint_inputs (h : cfg.Valid)
    (s a η : ℝ) (hs : 0 < s) (ha : 0 < a) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop,
      cfg.NativeFineJointCap k s (cfg.N k ^ (-r)) (cfg.N k ^ (-a)) ∧
      27648 * cfg.K k ^ 13 ≤ cfg.N k ^ η ∧
      (cfg.AssignmentLevel k s → cfg.JointMeshConditions k s r a) := by
  let r := 2 * (a + s + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hNone : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hc₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 1
    (show -r + s / 2 < -a by dsimp [r]; linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have hc₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 2
    (show -r + s < 0 by dsimp [r]; linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have hc₃ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    h.scale_limit (show -r < -s by dsimp [r]; linarith) (3 : ℝ)
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 13
    (show (0 : ℝ) < η from hη) (show (0 : ℝ) ≤ 27648 by norm_num)
  refine ⟨r, hr, ?_⟩
  filter_upwards [h.eventually_native_fine_joint_cap s r a hs.le hr ha, hc₁, hc₂, hc₃, hcost]
    with k hcap hk₁ hk₂ hk₃ hcost
  refine ⟨hcap, by simpa only [Real.rpow_zero, mul_one] using hcost.le, ?_⟩
  intro lev
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  let H := cfg.timeLength k s
  have hH : 0 < H := by dsimp [H, timeLength]; positivity
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  have he : cfg.κ * s = s / 2 := by rw [hκ]; ring
  have hHi : H⁻¹ ≤ cfg.K k * cfg.N k ^ (s / 2) := by
    simpa only [H, timeLength, inv_inv, he] using lev.time_upper
  have hcell : cfg.N k ^ (-r) ≤ H * cfg.N k ^ (-a) := by
    have hdiv : cfg.N k ^ (-r) / H ≤ cfg.N k ^ (-a) := by
      calc
        _ = cfg.N k ^ (-r) * H⁻¹ := by ring
        _ ≤ cfg.N k ^ (-r) * (cfg.K k * cfg.N k ^ (s / 2)) :=
          mul_le_mul_of_nonneg_left hHi (Real.rpow_nonneg hn.le _)
        _ = cfg.K k * cfg.N k ^ (-r + s / 2) := by rw [Real.rpow_add hn]; ring
        _ ≤ _ := by simpa only [pow_one, one_mul] using hk₁.le
    simpa only [mul_comm] using (div_le_iff₀ hH).mp hdiv
  have htrans : cfg.N k ^ (-r) ≤ H ^ 2 := by
    have hhalf : (cfg.N k ^ (s / 2)) ^ 2 = cfg.N k ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      ring
    have hdiv : cfg.N k ^ (-r) / H ^ 2 ≤ 1 := by
      calc
        _ = cfg.N k ^ (-r) * (H⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
        _ ≤ cfg.N k ^ (-r) * (cfg.K k * cfg.N k ^ (s / 2)) ^ 2 := by gcongr
        _ = cfg.K k ^ 2 * cfg.N k ^ (-r + s) := by
          rw [mul_pow, hhalf, Real.rpow_add hn]
          ring
        _ ≤ 1 := by simpa only [one_mul, Real.rpow_zero] using hk₂.le
    simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos hH)).mp hdiv
  have hg : H / cfg.K k ≤ cfg.N k ^ (-cfg.ℓ * s) := by
    rw [h.horizontal_rate]
    exact (time_length_comparison hn hK lev.time_lower lev.time_upper).1
  have hbase : H ^ 2 ≤ cfg.K k * H * cfg.N k ^ (-cfg.ℓ * s) := by
    have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hK).mp hg) hH.le
    nlinarith only [hm]
  exact ⟨hcell, htrans.trans hbase, hk₃.le⟩

/-- Every actual retained continuous law in a true label has the exact
normalized original-palette joint cap required by Row, with any prescribed
positive loss. This statement is independent of row-list preparation. -/
theorem Valid.eventually_normalized_label_joint_cap (h : cfg.Valid)
    (s a η : ℝ) (hs : 0 < s) (ha : 0 < a) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ (_lev : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
      (σ : Measure (α × ℝ)),
      σ ≤ (cfg.μ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) →
      ∀ (t₀ Z₀ : ℝ) (q : Fin 2 → ℤ) (j : ℤ),
      (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
        σ.map (unitTimeMap t₀ (cfg.timeLength k s)))
        (cfg.normalizedRowCell k (cfg.timeLength k s) t₀ Z₀ (cfg.N k ^ (-a)) q j) ≤
      ENNReal.ofReal (cfg.N k ^ η * (cfg.N k ^ (-a)) ^ 2) *
        cfg.π k (Ico ((j : ℝ) * cfg.N k ^ (-a)) (((j : ℝ) + 1) * cfg.N k ^ (-a))) := by
  obtain ⟨r, hr, hinputs⟩ := h.eventually_native_joint_inputs s a η hs ha hη
  filter_upwards [hinputs] with k hk
  intro lev i σ hσ t₀ Z₀ q j
  by_cases hBi : (cfg.B k s i).Nonempty
  swap
  · have he : cfg.B k s i = ∅ := not_nonempty_iff_eq_empty.mp hBi
    have hσzero : σ = 0 := le_antisymm
      (by simpa only [he, empty_prod, Measure.restrict_empty] using hσ)
      (by intro E; exact zero_le)
    simp [hσzero]
  obtain ⟨l₀, hl₀⟩ := hBi
  let tleft := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s
  have htleft : tleft ∈ I (cfg.T k s) (cfg.j k s i) := by
    refine ⟨le_rfl, ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  obtain ⟨L, _, hL, hfit⟩ := lev.active_affine_entry h hs.le i l₀ hl₀ tleft htleft
  have hfit' : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 - affineBaseValue L
        ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4]| ≤
          cfg.K k * cfg.N k ^ (-s) := by
    intro l hl t ht
    convert hfit l hl t ht using 1
    congr 1
    simp [affineBaseValue, affineResidualIntercept, affineResidualSlope, Fin.sum_univ_succ]
    ring
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  have hmesh := hk.2.2 lev
  have hcap := lev.normalized_label_joint_cap h i L hL hfit' σ hσ
    (cfg.N k ^ (-r)) (cfg.N k ^ (-a)) t₀ Z₀
    (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hn _)
    hmesh.1 hmesh.2.1 hmesh.2.2 hk.1 q j
  apply hcap.trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk.2.1 (sq_nonneg _))

end Data

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
