import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepPrune
import Submission.Lib.K4OutputReferenceMenus.WindowCaps

set_option linter.unusedVariables false

/-!
# Joint caps of moving boxes with a hidden window

The frozen joint caps at one index, integrated by the accepted
`K4OutputReferenceMenus.moving_box_signal_cap` over a moving base box with a hidden window
following a Lipschitz offset, with the original palette factor of one velocity bin or of any
set of velocity bins.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The frozen caps at index `k` for the range `R`. -/
def CapsAt (cfg : Data α) (k : ℕ) (R : ℝ) : Prop :=
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
    (∀ a : ℤ, cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = a} ≤
      ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v))) ∧
    (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) /
        (cfg.N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s))) ∧
    (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) /
        (cfg.N k ^ (-s))⌋ = a ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s)) *
        cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})

theorem capsAt_eventually {cfg : Data α} (hcaps : cfg.Caps) {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, CapsAt cfg k R := hcaps R hR

/-- The base point `(t, x₁, x₂)` of an incidence. -/
def basePoint (cfg : Data α) (k : ℕ) (p : α × ℝ) : Fin 3 → ℝ :=
  ![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3, cfg.b k p.1 1 + p.2 * cfg.b k p.1 4]

theorem z_eq_baseMesh (cfg : Data α) (k : ℕ) (r : ℝ) (p : α × ℝ) :
    cfg.z k (cfg.N k) r p = baseMesh (cfg.N k ^ (-r)) (basePoint cfg k p) := by
  funext e
  fin_cases e <;> simp [Data.z, baseMesh, basePoint, Data.x]

theorem rpow_cap_eq {N r s d : ℝ} (hN : 0 < N) :
    N ^ (-3 * r - d * s) = (N ^ (-r)) ^ 3 * (N ^ (-s)) ^ d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 1
  push_cast
  ring

/-- **Box cap with one velocity bin.**  A set of incidences whose base points lie in a moving
box and whose hidden coordinate lies in a window of width `N^-s'` above a Lipschitz offset,
all in one velocity bin, has mass at most `6000 K radius width₀ width₁ (N^-s')^d π(bin)`. -/
theorem box_cap_bin {cfg : Data α} {k : ℕ} {R : ℝ} (hcap : CapsAt cfg k R) (hN : 0 < cfg.N k)
    (hK : 0 ≤ cfg.K k) (hb : Measurable (cfg.b k)) {r s' v' : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R)
    (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (E : Set (α × ℝ)) (offset : (Fin 3 → ℝ) → ℝ) {θo radius L : ℝ}
    (hθ : 0 ≤ θo) (hθa : θo ≤ cfg.N k ^ (-s')) (hdr : cfg.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, cfg.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * cfg.N k ^ (-r) ≤ width i)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePoint cfg k p i - y i| ≤ cfg.N k ^ (-r)) →
      |offset (basePoint cfg k p) - offset y| ≤ θo)
    (hE : ∀ p ∈ E, basePoint cfg k p ∈ movingBox time radius center velocity width ∧
      offset (basePoint cfg k p) ≤ cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ∧
      cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ≤ offset (basePoint cfg k p) + cfg.N k ^ (-s'))
    (v₀ : ℤ) (hEv : ∀ p ∈ E, ⌊cfg.b k p.1 3 / cfg.N k ^ (-v')⌋ = v₀) :
    cfg.μ k E ≤ ENNReal.ofReal (6000 * cfg.K k * radius * width 0 * width 1 *
      (cfg.N k ^ (-s')) ^ cfg.d) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v'))⌋ = v₀} := by
  set V := {p : α × ℝ | ⌊cfg.b k p.1 3 / cfg.N k ^ (-v')⌋ = v₀} with hVdef
  have hVm : MeasurableSet V :=
    ((((measurable_pi_apply 3).comp hb).comp measurable_fst).div_const _).floor
      (measurableSet_singleton v₀)
  have hEV : cfg.μ k E ≤ (cfg.μ k).restrict V E := by
    rw [Measure.restrict_apply' hVm]
    exact measure_mono fun p hp => ⟨hp, hEv p hp⟩
  refine hEV.trans ?_
  have hr0 : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have ha0 : 0 < cfg.N k ^ (-s') := Real.rpow_pos_of_pos hN _
  apply Submission.Lib.K4OutputReferenceMenus.moving_box_signal_cap ((cfg.μ k).restrict V)
    (basePoint cfg k) (fun p => cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) offset E hr0 ha0 hθ hθa hdr
    hL hK time center velocity width hv hdw hmove ho hE
  intro c j
  rw [Measure.restrict_apply' hVm]
  have hset : {p : α × ℝ | baseMesh (cfg.N k ^ (-r)) (basePoint cfg k p) = c ∧
      ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / cfg.N k ^ (-s')⌋ = j} ∩ V =
      {p | cfg.z k (cfg.N k) r p = c ∧
        ⌊(if false then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) /
          (cfg.N k ^ (-s'))⌋ = j ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v'))⌋ = v₀} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, z_eq_baseMesh, hVdef, Bool.false_eq_true, ite_false,
      Data.x, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, and_assoc]
  rw [hset]
  calc _ ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s')) *
        cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v'))⌋ = v₀} :=
        (hcap r s' v' hr1 hr2 hs1 hs2 hv1 hv2).2.2 false c j v₀
    _ = _ := by rw [rpow_cap_eq hN, mul_assoc]

/-- **Box cap with a set of velocity bins.** -/
theorem box_cap_bins {cfg : Data α} {k : ℕ} {R : ℝ} (hcap : CapsAt cfg k R) (hN : 0 < cfg.N k)
    (hK : 0 ≤ cfg.K k) (hb : Measurable (cfg.b k)) {r s' v' : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R)
    (hs1 : 0 ≤ s') (hs2 : s' ≤ R) (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (E : Set (α × ℝ)) (offset : (Fin 3 → ℝ) → ℝ) {θo radius L : ℝ}
    (hθ : 0 ≤ θo) (hθa : θo ≤ cfg.N k ^ (-s')) (hdr : cfg.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, cfg.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * cfg.N k ^ (-r) ≤ width i)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePoint cfg k p i - y i| ≤ cfg.N k ^ (-r)) →
      |offset (basePoint cfg k p) - offset y| ≤ θo)
    (hE : ∀ p ∈ E, basePoint cfg k p ∈ movingBox time radius center velocity width ∧
      offset (basePoint cfg k p) ≤ cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ∧
      cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ≤ offset (basePoint cfg k p) + cfg.N k ^ (-s'))
    (A : Set ℤ) :
    cfg.μ k {p | p ∈ E ∧ vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ A} ≤
      ENNReal.ofReal (6000 * cfg.K k * radius * width 0 * width 1 *
        (cfg.N k ^ (-s')) ^ cfg.d) * paletteBins (cfg.π k) (cfg.N k ^ (-v')) A := by
  apply bin_cap_of_singletons (cfg.μ k) E (fun p => cfg.b k p.1 3) (cfg.π k) _ _ _ A
  intro a
  apply box_cap_bin hcap hN hK hb hr1 hr2 hs1 hs2 hv1 hv2 {p | p ∈ E ∧ ⌊cfg.b k p.1 3 / cfg.N k ^ (-v')⌋ = a}
    offset hθ hθa hdr hL time center velocity width hv hdw hmove
    (fun p hp => ho p hp.1) (fun p hp => hE p hp.1) a (fun p hp => hp.2)

/-- **Box cap over all velocities.** -/
theorem box_cap {cfg : Data α} {k : ℕ} {R : ℝ} (hcap : CapsAt cfg k R) (hN : 0 < cfg.N k)
    (hK : 0 ≤ cfg.K k) (hb : Measurable (cfg.b k)) (hπ : IsProbabilityMeasure (cfg.π k))
    {r s' v' : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R)
    (hs1 : 0 ≤ s') (hs2 : s' ≤ R) (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (E : Set (α × ℝ)) (offset : (Fin 3 → ℝ) → ℝ) {θo radius L : ℝ}
    (hθ : 0 ≤ θo) (hθa : θo ≤ cfg.N k ^ (-s')) (hdr : cfg.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, cfg.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * cfg.N k ^ (-r) ≤ width i)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePoint cfg k p i - y i| ≤ cfg.N k ^ (-r)) →
      |offset (basePoint cfg k p) - offset y| ≤ θo)
    (hE : ∀ p ∈ E, basePoint cfg k p ∈ movingBox time radius center velocity width ∧
      offset (basePoint cfg k p) ≤ cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ∧
      cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 ≤ offset (basePoint cfg k p) + cfg.N k ^ (-s')) :
    cfg.μ k E ≤ ENNReal.ofReal (6000 * cfg.K k * radius * width 0 * width 1 *
      (cfg.N k ^ (-s')) ^ cfg.d) := by
  have h := box_cap_bins hcap hN hK hb hr1 hr2 hs1 hs2 hv1 hv2 E offset hθ hθa hdr hL time center
    velocity width hv hdw hmove ho hE univ
  have hset : {p | p ∈ E ∧ vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ (univ : Set ℤ)} = E := by
    ext p; simp
  rw [hset] at h
  have hone : paletteBins (cfg.π k) (cfg.N k ^ (-v')) univ = 1 := by
    rw [paletteBins, Measure.map_apply (measurable_vbin _) MeasurableSet.univ, preimage_univ,
      measure_univ]
  rw [hone, mul_one] at h
  exact h

theorem abs_sub_center_of_floor {y w : ℝ} {Q : ℤ} (hw : 0 < w) (h : ⌊y / w⌋ = Q) :
    |y - w * ((Q : ℝ) + 1 / 2)| ≤ w / 2 := by
  have h1 := Int.floor_le (y / w)
  have h2 := Int.lt_floor_add_one (y / w)
  rw [h] at h1 h2
  rw [le_div_iff₀ hw] at h1
  rw [div_lt_iff₀ hw] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- **The cap of one normalized base cell of a true block** (the field's fine base cell). -/
theorem block_cell_cap {cfg : Data α} {k : ℕ} {s R : ℝ} (hcap : CapsAt cfg k R)
    (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hb : Measurable (cfg.b k))
    (hπ : IsProbabilityMeasure (cfg.π k))
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L) {Lb : ℝ}
    (hLb : ∀ e, |L e| ≤ Lb) {δ r s' : ℝ} (hδ : 0 < δ)
    (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R) (hR1 : R⁻¹ ≤ 1) (hR : 1 ≤ R)
    (ha' : 2 * cfg.K k * cfg.N k ^ (-s) ≤ cfg.N k ^ (-s'))
    (hmesh : (cfg.K k + cfg.K k ^ 2 + 1) * cfg.N k ^ (-r) ≤ ((2 : ℝ) ^ cfg.T k s)⁻¹ * δ / 2)
    (hlip : 3 * Lb * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s')) (Q : Fin 2 → ℤ) :
    cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
      ⌊(p.2 - (cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s) / ((2 : ℝ) ^ cfg.T k s)⁻¹ / δ⌋ = Q 0 ∧
      ⌊(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - cfg.c k s i 0 - p.2 * cfg.c k s i 1) /
        ((2 : ℝ) ^ cfg.T k s)⁻¹ / δ⌋ = Q 1} ≤
      ENNReal.ofReal (6000 * cfg.K k * (((2 : ℝ) ^ cfg.T k s)⁻¹ * δ / 2) *
        (((2 : ℝ) ^ cfg.T k s)⁻¹ * δ / 2) *
        (cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.κ * s) +
          cfg.K k * (((2 : ℝ) ^ cfg.T k s)⁻¹ * δ / 2)) * (cfg.N k ^ (-s')) ^ cfg.d) := by
  set q := ((2 : ℝ) ^ cfg.T k s)⁻¹ with hqdef
  set t₀ := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s with ht₀def
  set c := cfg.c k s i with hcdef
  set K := cfg.K k with hKdef
  have hq : 0 < q := by positivity
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hqδ : 0 < q * δ := mul_pos hq hδ
  have hr0 : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
  let center : Fin 2 → ℝ := ![c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2),
    c 2 + c 4 * (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2))]
  let velocity : Fin 2 → ℝ := ![c 1, c 3 + c 4 * c 1]
  let width : Fin 2 → ℝ := ![q * δ / 2, K * q * cfg.N k ^ (-cfg.κ * s) + K * (q * δ / 2)]
  have hc : ∀ e, |c e| ≤ K := fun e => hB.c_bd i e
  have hvel : ∀ e, |velocity e| ≤ K + K ^ 2 := by
    intro e
    fin_cases e
    · simp only [velocity, Fin.zero_eta, Matrix.cons_val_zero]
      have := hc 1
      nlinarith [sq_nonneg K]
    · simp only [velocity, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
      calc |c 3 + c 4 * c 1| ≤ |c 3| + |c 4| * |c 1| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ K + K * K := by gcongr <;> exact hc _
        _ = K + K ^ 2 := by ring
  have hgpos : 0 < cfg.N k ^ (-cfg.κ * s) := Real.rpow_pos_of_pos hN _
  have hKK : 0 ≤ K + K ^ 2 := by positivity
  have hmesh' : (K + K ^ 2) * cfg.N k ^ (-r) ≤ q * δ / 2 := by
    have : (K + K ^ 2) * cfg.N k ^ (-r) ≤ (K + K ^ 2 + 1) * cfg.N k ^ (-r) := by nlinarith
    exact this.trans hmesh
  have hwidth0 : cfg.N k ^ (-r) ≤ q * δ / 2 := by
    have : cfg.N k ^ (-r) ≤ (K + K ^ 2 + 1) * cfg.N k ^ (-r) := by nlinarith
    exact this.trans hmesh
  have hKqδ : q * δ / 2 ≤ K * (q * δ / 2) := le_mul_of_one_le_left (by positivity) hK
  have hKqg : 0 ≤ K * q * cfg.N k ^ (-cfg.κ * s) := by positivity
  have hdw : ∀ e, cfg.N k ^ (-r) ≤ width e := by
    intro e; fin_cases e
    · simpa [width] using hwidth0
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      linarith
  have hmove : ∀ e, (K + K ^ 2) * cfg.N k ^ (-r) ≤ width e := by
    intro e; fin_cases e
    · simpa [width] using hmesh'
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      linarith
  have h := box_cap hcap hN hK0 hb hπ hr1 hr2 hs1 hs2 hR1 hR
    {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
      ⌊(p.2 - t₀) / q / δ⌋ = Q 0 ∧ ⌊(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - c 0 - p.2 * c 1) / q / δ⌋ = Q 1}
    (fun y => (L 0 + L 1 * y 0 + L 2 * y 1 + L 3 * y 2) - K * cfg.N k ^ (-s))
    (θo := 3 * Lb * cfg.N k ^ (-r)) (by positivity) hlip hwidth0 (by positivity)
    (t₀ + q * δ * ((Q 0 : ℝ) + 1 / 2)) center velocity width hvel hdw hmove ?_ ?_
  · simpa only [width, center, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  · -- Lipschitz offset
    intro p _ y hy
    have e : (L 0 + L 1 * basePoint cfg k p 0 + L 2 * basePoint cfg k p 1 + L 3 * basePoint cfg k p 2 -
        K * cfg.N k ^ (-s)) - (L 0 + L 1 * y 0 + L 2 * y 1 + L 3 * y 2 - K * cfg.N k ^ (-s)) =
        L 1 * (basePoint cfg k p 0 - y 0) + L 2 * (basePoint cfg k p 1 - y 1) +
          L 3 * (basePoint cfg k p 2 - y 2) := by ring
    simp only [e]
    calc _ ≤ |L 1| * |basePoint cfg k p 0 - y 0| + |L 2| * |basePoint cfg k p 1 - y 1| +
          |L 3| * |basePoint cfg k p 2 - y 2| := by
          refine (abs_add_three _ _ _).trans ?_; simp only [abs_mul, le_refl]
      _ ≤ Lb * cfg.N k ^ (-r) + Lb * cfg.N k ^ (-r) + Lb * cfg.N k ^ (-r) := by
          gcongr
          · exact hLb 1
          · exact hy 0
          · exact hLb 2
          · exact hy 1
          · exact hLb 3
          · exact hy 2
      _ = 3 * Lb * cfg.N k ^ (-r) := by ring
  · -- membership
    rintro ⟨l, t⟩ ⟨hl, ht, hQ0, hQ1⟩
    simp only at hl ht hQ0 hQ1
    obtain ⟨hx, hy, -⟩ := hB.geom i l ((hB.sets i).2.2 hl) t ht
    have hfit := (hB.fit i l hl t ht).1
    rw [eval_horizontalForm hL] at hfit
    simp only [Data.x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hx hy hfit
    have ht' : |(t - t₀) / q - δ * ((Q 0 : ℝ) + 1 / 2)| ≤ δ / 2 := by
      have := abs_sub_center_of_floor hδ hQ0
      exact this
    have hx' : |(cfg.b k l 0 + t * cfg.b k l 3 - c 0 - t * c 1) / q - δ * ((Q 1 : ℝ) + 1 / 2)| ≤ δ / 2 :=
      abs_sub_center_of_floor hδ hQ1
    have ht'' : |t - (t₀ + q * δ * ((Q 0 : ℝ) + 1 / 2))| ≤ q * δ / 2 := by
      have e : t - (t₀ + q * δ * ((Q 0 : ℝ) + 1 / 2)) = q * ((t - t₀) / q - δ * ((Q 0 : ℝ) + 1 / 2)) := by
        field_simp; ring
      rw [e, abs_mul, abs_of_pos hq]
      calc q * |(t - t₀) / q - δ * ((Q 0 : ℝ) + 1 / 2)| ≤ q * (δ / 2) := by gcongr
        _ = q * δ / 2 := by ring
    have hx'' : |cfg.b k l 0 + t * cfg.b k l 3 - (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2) + t * c 1)| ≤
        q * δ / 2 := by
      have e : cfg.b k l 0 + t * cfg.b k l 3 - (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2) + t * c 1) =
          q * ((cfg.b k l 0 + t * cfg.b k l 3 - c 0 - t * c 1) / q - δ * ((Q 1 : ℝ) + 1 / 2)) := by
        field_simp; ring
      rw [e, abs_mul, abs_of_pos hq]
      calc q * |(cfg.b k l 0 + t * cfg.b k l 3 - c 0 - t * c 1) / q - δ * ((Q 1 : ℝ) + 1 / 2)| ≤
          q * (δ / 2) := by gcongr
        _ = q * δ / 2 := by ring
    have hy'' : |cfg.b k l 1 + t * cfg.b k l 4 - (c 2 + c 4 * (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2)) +
        t * (c 3 + c 4 * c 1))| ≤ K * q * cfg.N k ^ (-cfg.κ * s) + K * (q * δ / 2) := by
      have e : cfg.b k l 1 + t * cfg.b k l 4 - (c 2 + c 4 * (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2)) +
          t * (c 3 + c 4 * c 1)) = (cfg.b k l 1 + t * cfg.b k l 4 - c 2 - t * c 3 -
            c 4 * (cfg.b k l 0 + t * cfg.b k l 3)) +
          c 4 * (cfg.b k l 0 + t * cfg.b k l 3 - (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2) + t * c 1)) := by
        ring
      rw [e]
      calc _ ≤ |cfg.b k l 1 + t * cfg.b k l 4 - c 2 - t * c 3 - c 4 * (cfg.b k l 0 + t * cfg.b k l 3)| +
            |c 4| * |cfg.b k l 0 + t * cfg.b k l 3 - (c 0 + q * δ * ((Q 1 : ℝ) + 1 / 2) + t * c 1)| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ K * q * cfg.N k ^ (-cfg.κ * s) + K * (q * δ / 2) := by
            gcongr
            exact hc 4
    refine ⟨?_, ?_, ?_⟩
    · simp only [basePoint, movingBox, mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Matrix.cons_val_two, Matrix.tail_cons, center, velocity, width]
      refine ⟨ht'', ?_, ?_⟩
      · simpa [mul_comm] using hx''
      · simpa [mul_comm] using hy''
    · simp only [basePoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [← hKdef] at hfit
      have := (abs_le.mp hfit).1
      linarith
    · simp only [basePoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [← hKdef] at hfit
      have := (abs_le.mp hfit).2
      linarith

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
