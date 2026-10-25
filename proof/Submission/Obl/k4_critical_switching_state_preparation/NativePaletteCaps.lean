/- Adapted from this LOT tree, obligation o201, session x0697, commit d395b4346c32,
   Submission/Obl/k4_horizontal_critical_rate_candidates/NativePaletteCaps.lean.
   Rebased from its midpoint frame to our frozen left-endpoint frame; the normalized
   position bound is K^2 and the predictor slope bound is 12*K*H*M. -/
import Submission.Obl.k4_critical_switching_state_preparation.NativeCellCaps
import Submission.Obl.k4_critical_switching_state_preparation.JointSource

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Exactly the native-hidden/velocity alternative of the frozen joint caps. -/
def JointPaletteCap (cfg : Data α) (k : ℕ) (r t v : ℝ) : Prop :=
  ∀ (q : Fin 3 → ℤ) (j z : ℤ),
    cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧
      ⌊(cfg.x k p.1 p.2) 3 / cfg.N k ^ (-t)⌋ = j ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋ = z} ≤
        ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * t)) *
          cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = z}

theorem Valid.eventually_joint_palette_cap (valid : cfg.Valid) {r t v : ℝ}
    (hr : 0 < r) (ht : 0 ≤ t) (hv : 0 < v) :
    ∀ᶠ k in atTop, cfg.JointPaletteCap k r t v := by
  let R := 2 + r + t + v + r⁻¹ + v⁻¹
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hvinv : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith
  have hrR : r ≤ R := by dsimp [R]; linarith
  have htR : t ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := (inv_le_comm₀ (by linarith) hr).mpr (by dsimp [R]; linarith)
  have hRv : R⁻¹ ≤ v := (inv_le_comm₀ (by linarith) hv).mpr (by dsimp [R]; linarith)
  filter_upwards [valid.caps R hR] with k hk
  intro q j z
  simpa using (hk r t v hRr hrR ht htR hRv hvR).2.2 false q j z

/-- Write the frozen mesh coefficient in volume-times-hidden-scale form. -/
theorem joint_palette_scale_factor (N K d r t : ℝ) (hN : 0 < N) :
    K * (N ^ (-r)) ^ 3 * (N ^ (-t)) ^ d = K * N ^ (-3 * r - d * t) := by
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul hN.le, mul_assoc,
    ← Real.rpow_add hN]
  congr 1
  ring

/-- The native joint cap on an ACTUAL original midpoint/base pair. All
geometric hypotheses are supplied by its original true parent. The original
velocity palette is retained, with the contact-volume factor q_s^4. -/
theorem AssignmentLevel.original_pair_palette_cap (valid : cfg.Valid) {k : ℕ} {s t r v : ℝ}
    (parent : cfg.AssignmentLevel k s) (ip : Fin (cfg.n k s))
    (cap : cfg.JointPaletteCap k r t v) (A : Fin 4 → ℝ) (E : Set (α × ℝ))
    (δ M err Kmesh : ℝ) (u : ℤ × (Fin 3 → ℤ)) (p₀ : α × ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hKmesh : 0 ≤ Kmesh)
    (hp₀ : p₀ ∈ E) (hcode₀ : cfg.sourcePair k s ip A (cfg.N k ^ (-t)) δ p₀ = u)
    (hA : ∀ e : Fin 3, |A e.succ| ≤ M)
    (hE : ∀ p ∈ E, p.1 ∈ cfg.B k s ip ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s ip) ∧
      |affineResidualSlope A (cfg.b k p.1)| ≤ err)
    (hmesh : 3 * (12 * cfg.K k * cfg.timeLength k s * M) * δ ≤ Kmesh * cfg.N k ^ (-t))
    (hsmall : cfg.timeLength k s * err ≤ cfg.K k * cfg.N k ^ (-t))
    (hξt : cfg.N k ^ (-r) ≤ cfg.timeLength k s * δ)
    (hξZ : 6 * cfg.K k * cfg.N k ^ (-r) ≤ cfg.timeLength k s * δ)
    (hξY : 9 * cfg.K k * cfg.N k ^ (-r) ≤
      (cfg.K k ^ 2 + 2) * cfg.timeLength k s ^ 2 * δ) :
    ∀ z : ℤ, cfg.μ k {p | p ∈ E ∧ cfg.sourcePair k s ip A (cfg.N k ^ (-t)) δ p = u ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋ = z} ≤
      ENNReal.ofReal (128 * cfg.K k * (cfg.K k ^ 2 + 2) * (Kmesh + cfg.K k + 2) *
        cfg.timeLength k s ^ 4 * δ ^ 3 * (cfg.N k ^ (-t)) ^ cfg.d) *
          cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = z} := by
  have hN : 0 < cfg.N k := by linarith [valid.scale k]
  have hK : 1 ≤ cfg.K k := valid.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hq := cfg.timeLength_pos k s
  let H := cfg.timeLength k s
  let t₀ := cfg.blockLeft k s ip
  let tm := cfg.midpoint k s ip
  let c := cfg.c k s ip
  let z₀ := c 0 + t₀ * c 1
  let y₀ := c 2 + t₀ * c 3 + c 4 * z₀
  let point (p : α × ℝ) := cfg.parentFrame k s ip (nativeHorizontalLine (cfg.b k p.1) p.2)
  let q₀ := point p₀
  let S := 12 * cfg.K k * H * M
  let a := cfg.N k ^ (-t)
  let D := Kmesh + cfg.K k + 1
  let center := affineBaseEval (normalizedPredictor H t₀ z₀ y₀ (c 1) A) q₀ + a * u.1
  let cell := {p | p ∈ E ∧ cfg.sourcePair k s ip A (cfg.N k ^ (-t)) δ p = u}
  have hunframe (p : α × ℝ) : horizontalUnframe H t₀ z₀ y₀ (c 1) (point p) =
      nativeHorizontalLine (cfg.b k p.1) p.2 :=
    horizontalUnframe_frame H t₀ z₀ y₀ (c 1) hq.ne' _
  have hcell (p) (hp : p ∈ cell) : point p ∈ contactGridCell δ u.2 := by
    intro i
    exact congrFun (congrArg Prod.snd hp.2) i
  have hgap (p) (hp : p ∈ cell) : ∀ i, |point p i - q₀ i| ≤ δ :=
    contactGridCell_coordinate_gap hδ (hcell p hp) (hcell p₀ ⟨hp₀, hcode₀⟩)
  have hparam := parent.blockOrigin_bounds valid ip
  have hpred₀ := normalizedPredictor_slope_bound H t₀ z₀ y₀ (c 1) (3 * cfg.K k) M A
    hq.le (cfg.timeLength_le_one k s) (by linarith) hM
    hparam.1 hparam.2.1 (hparam.2.2.trans (by linarith)) hA
  have hpred (e : Fin 3) : |normalizedPredictor H t₀ z₀ y₀ (c 1) A e.succ| ≤ S := by
    convert hpred₀ e using 1; ring
  have hvalue (p) (hp : p ∈ cell) : |(cfg.x k p.1 p.2) 3 - center| ≤ D * a := by
    have htime := mem_I_time_gap _ _ (hE p hp.1).2.1
    change |p.2 - tm| ≤ H / 2 at htime
    have htime' : |p.2 - tm| ≤ H := by linarith
    have hb : ⌊(affineResidualIntercept A (cfg.b k p.1) +
        tm * affineResidualSlope A (cfg.b k p.1)) / a⌋ = u.1 := congrArg Prod.fst hp.2
    have hvp := native_hidden_value_in_midpoint_cell A (cfg.b k p.1) q₀
      H t₀ z₀ y₀ (c 1) tm p.2 S δ a err u.1 hq (by dsimp [S, H]; positivity)
      (Real.rpow_pos_of_pos hN _) hpred (hgap p hp) (hE p hp.1).2.2 htime' hb
    exact hvp.trans (by dsimp [S, D, a, H] at *; nlinarith only [hmesh, hsmall])
  have hunit := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit _ _ (hE p₀ hp₀).2.1
  have hphysicaltime : |horizontalUnframe H t₀ z₀ y₀ (c 1) q₀ 0| ≤ 1 := by
    rw [hunframe p₀]
    change |p₀.2| ≤ 1
    simpa only [abs_of_nonneg hunit.1] using hunit.2
  have hphysicalposition : |horizontalUnframe H t₀ z₀ y₀ (c 1) q₀ 1| ≤ 3 * cfg.K k := by
    rw [hunframe p₀]
    exact (parent.native_base_bounds valid ip p₀.1
      (parent.fitted_subset ip (hE p₀ hp₀).1) (hE p₀ hp₀).2.1).1
  have hnative (q : Fin 3 → ℤ) (j z : ℤ) :
      cfg.μ k {p | (fun i => ⌊horizontalUnframe H t₀ z₀ y₀ (c 1) (point p) i /
        cfg.N k ^ (-r)⌋) = q ∧ ⌊(cfg.x k p.1 p.2) 3 / a⌋ = j ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋ = z} ≤
      ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ 3 * a ^ cfg.d) *
        cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = z} := by
    rw [joint_palette_scale_factor _ _ _ _ _ hN]
    have hcodes (p : α × ℝ) :
        (fun i => ⌊horizontalUnframe H t₀ z₀ y₀ (c 1) (point p) i / cfg.N k ^ (-r)⌋) =
          cfg.z k (cfg.N k) r p := by rw [hunframe p]; rfl
    simpa only [hcodes] using cap q j z
  have hbound := native_joint_cap_normalized_cell (cfg.μ k) cell point
    (fun p => (cfg.x k p.1 p.2) 3) (fun p => ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋)
    (fun z => cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = z})
    H t₀ z₀ y₀ (c 1) (cfg.K k ^ 2) (3 * cfg.K k) δ (cfg.N k ^ (-r)) a cfg.d center D
    (cfg.K k) q₀ hq.le (sq_nonneg _) hδ.le (by linarith) (Real.rpow_pos_of_pos hN _)
    (Real.rpow_pos_of_pos hN _) (by dsimp [D]; positivity) hK0 hξt
    (by convert hξZ using 1; ring) (by convert hξY using 1; ring)
    (by
      have hh := (parent.framedPoint_bounds valid ip
        (parent.fitted_subset ip (hE p₀ hp₀).1) (hE p₀ hp₀).2.1).1
      change |cfg.framedPoint k s ip p₀ 0| ≤ 1
      rw [abs_of_nonneg hh.1]
      exact hh.2)
    (parent.framedPoint_bounds valid ip
      (parent.fitted_subset ip (hE p₀ hp₀).1) (hE p₀ hp₀).2.1).2.1
    hphysicaltime ((parent.coefficient_bound ip 1).trans (by linarith)) hphysicalposition
    hgap hvalue hnative
  intro z
  simpa only [cell, D, a, H, mem_ofPred_eq, and_assoc,
    show Kmesh + cfg.K k + 1 + 1 = Kmesh + cfg.K k + 2 by ring] using hbound z

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
