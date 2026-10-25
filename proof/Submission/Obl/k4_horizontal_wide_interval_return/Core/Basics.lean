import Submission.Obl.k4_horizontal_wide_interval_return.Model
import Submission.Lib.K4OutputReferenceMenus.WindowCaps

/-!
# Basic access to the frozen caps for the wide-interval core

`basePt` and `hidden` are the base point `(t, Z, Y)` and the hidden value `X` of an
incidence `(l, t)` along the trajectory `t ↦ (t, b₀ + t b₃, b₁ + t b₄, b₂ + t b₅)`.
`JointCapAt` is the frozen joint cap at one triple of resolutions, and
`strip_window_cap` charges a moving hidden window over a moving base box to it, keeping
the original palette weight (an application of the accepted
`K4OutputReferenceMenus.moving_box_signal_cap`).
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes Submission.Lib.K4OutputReferenceMenus

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The base point `(t, Z, Y)` of an incidence. -/
def basePt (b : α → Fin 6 → ℝ) (p : α × ℝ) : Fin 3 → ℝ :=
  ![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4]

/-- The hidden value `X` of an incidence. -/
def hidden (b : α → Fin 6 → ℝ) (p : α × ℝ) : ℝ := b p.1 2 + p.2 * b p.1 5

/-- The frozen joint cap at base cells `N^-r`, hidden bins `N^-s'`, velocity bins `N^-v'`. -/
def JointCapAt (μ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (N K d r s' v' : ℝ) : Prop :=
  ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
    μ {p | baseMesh (N ^ (-r)) (basePt b p) = q ∧ ⌊hidden b p / N ^ (-s')⌋ = a ∧
      ⌊b p.1 3 / N ^ (-v')⌋ = v₀} ≤
      ENNReal.ofReal (K * N ^ (-3 * r - d * s')) * π {w | ⌊w / N ^ (-v')⌋ = v₀}

theorem z_eq_baseMesh (cfg : Data α) (k : ℕ) (Nk r : ℝ) (p : α × ℝ) :
    cfg.z k Nk r p = baseMesh (Nk ^ (-r)) (basePt (cfg.b k) p) := by
  funext e
  fin_cases e <;> rfl

theorem x_three (cfg : Data α) (k : ℕ) (p : α × ℝ) :
    (cfg.x k p.1 p.2) 3 = hidden (cfg.b k) p := rfl

/-- The joint caps of a valid model, at all resolutions in a compact range. -/
theorem jointCapAt_eventually (cfg : Data α) (hv : cfg.Valid) {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ r s' v' : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s' → s' ≤ R → R⁻¹ ≤ v' → v' ≤ R →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' v' := by
  filter_upwards [hv.caps R hR] with k hk
  intro r s' v' hr1 hr2 hs1 hs2 hv1 hv2 q a v₀
  have h := (hk r s' v' hr1 hr2 hs1 hs2 hv1 hv2).2.2 false q a v₀
  simp only [Bool.false_eq_true, ↓reduceIte, z_eq_baseMesh, x_three] at h
  exact h

theorem rpow_cap_split {N : ℝ} (hN : 0 < N) (r s' d : ℝ) :
    N ^ (-3 * r - d * s') = (N ^ (-r)) ^ 3 * (N ^ (-s')) ^ d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
    ← Real.rpow_add hN]
  congr 1
  push_cast
  ring

theorem measurable_velocityBin {b : α → Fin 6 → ℝ} (hb : Measurable b) (c : ℝ) (v₀ : ℤ) :
    MeasurableSet {p : α × ℝ | ⌊b p.1 3 / c⌋ = v₀} := by
  have hm : Measurable fun p : α × ℝ => ⌊b p.1 3 / c⌋ :=
    Int.measurable_floor.comp
      (((measurable_pi_apply 3).comp (hb.comp measurable_fst)).div_const c)
  exact hm (measurableSet_singleton v₀)

/-- **Strip window cap.** A moving hidden window of width one hidden bin over a moving
base box of time radius `1/2` around `1/2`, inside one velocity bin, is charged to the
frozen joint caps; the original palette weight of the velocity bin is kept. -/
theorem strip_window_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v')
    (v₀ : ℤ) (offset : (Fin 3 → ℝ) → ℝ) (E : Set (α × ℝ))
    {θ L : ℝ} (hθ : 0 ≤ θ) (hθa : θ ≤ N ^ (-s')) (hL : 0 ≤ L)
    (center velocity width : Fin 2 → ℝ)
    (hvel : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, N ^ (-r) ≤ width i)
    (hmove : ∀ i, L * N ^ (-r) ≤ width i) (hdr : N ^ (-r) ≤ 1 / 2)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePt b p i - y i| ≤ N ^ (-r)) →
      |offset (basePt b p) - offset y| ≤ θ)
    (hE : ∀ p ∈ E, ⌊b p.1 3 / N ^ (-v')⌋ = v₀ ∧
      basePt b p ∈ movingBox (1 / 2) (1 / 2) center velocity width ∧
      offset (basePt b p) ≤ hidden b p ∧ hidden b p ≤ offset (basePt b p) + N ^ (-s')) :
    μ E ≤ ENNReal.ofReal (3000 * K * width 0 * width 1 * (N ^ (-s')) ^ d) *
      π {w | ⌊w / N ^ (-v')⌋ = v₀} := by
  set S : Set (α × ℝ) := {p | ⌊b p.1 3 / N ^ (-v')⌋ = v₀} with hSdef
  have hS : MeasurableSet S := measurable_velocityBin hb _ v₀
  have hES : E ⊆ S := fun p hp => (hE p hp).1
  have hrestr : μ E = μ.restrict S E := by
    rw [Measure.restrict_apply' hS, inter_eq_left.mpr hES]
  rw [hrestr]
  have hmain := moving_box_signal_cap (μ.restrict S) (basePt b) (hidden b) offset E
    (δ := N ^ (-r)) (a := N ^ (-s')) (θ := θ) (radius := 1 / 2) (L := L) (C := K) (d := d)
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _) hθ hθa hdr hL hK
    (1 / 2) center velocity width hvel hdw hmove ho
    (fun p hp => (hE p hp).2) (π {w | ⌊w / N ^ (-v')⌋ = v₀}) ?_
  · refine hmain.trans (le_of_eq ?_)
    congr 2
    ring
  · intro c j
    rw [Measure.restrict_apply' hS]
    have hsub : {p : α × ℝ | baseMesh (N ^ (-r)) (basePt b p) = c ∧
        ⌊hidden b p / N ^ (-s')⌋ = j} ∩ S =
        {p | baseMesh (N ^ (-r)) (basePt b p) = c ∧ ⌊hidden b p / N ^ (-s')⌋ = j ∧
          ⌊b p.1 3 / N ^ (-v')⌋ = v₀} := by
      ext p
      simp only [mem_inter_iff, mem_setOf_eq, hSdef]
      tauto
    rw [hsub]
    refine (hcap c j v₀).trans (le_of_eq ?_)
    rw [rpow_cap_split hN]
    congr 2
    ring

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
