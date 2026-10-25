/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/KeyCaps.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Keys
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.Basics

set_option autoImplicit false

/-!
# Caps over slot keys

Incidences of labels of one slot key, during the slot, whose slice coordinate lies in a
subinterval `[x - w, x]` and whose hidden value lies within `W` of a slowly varying offset of the
base point, are charged to the frozen joint cap through the accepted
`K4OutputReferenceMenus.moving_box_signal_cap`, keeping the palette weight of the key's velocity
bin.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes Submission.Lib.K4OutputReferenceMenus
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- **Key window cap.** -/
theorem key_window_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v') (κ : Fin 3 → ℤ) {t₀ q m x w ζ L : ℝ}
    (off : (Fin 3 → ℝ) → ℝ) (E : Set (α × ℝ))
    (hq : 0 < q) (hm : 0 < m) (hw : 0 ≤ w) (hζ : 0 ≤ ζ) (hL : 0 ≤ L)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ L) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ L)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (hmZ : L * N ^ (-r) ≤ 2 * N ^ (-v')) (hmY : L * N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePt b p i - y i| ≤ N ^ (-r)) →
      |off (basePt b p) - off y| ≤ N ^ (-s'))
    (hE : ∀ p ∈ E, slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      sliceY b m t₀ p.1 ∈ Icc (x - w) x ∧ |b p.1 4 + b p.1 0| ≤ ζ ∧
      |hidden b p - off (basePt b p)| ≤ N ^ (-s')) :
    μ E ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * (m * w + q * (ζ + N ^ (-v'))) *
      (N ^ (-s')) ^ d) * π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  set χ := N ^ (-v') with hχdef
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  set a := N ^ (-s') with hadef
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  set δ := N ^ (-r) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  set WY := m * w + q * (ζ + χ) with hWY
  -- the moving box
  let center : Fin 2 → ℝ := ![(κ 1 : ℝ) * χ, (κ 2 : ℝ) * m + 2 * m * (x - w / 2 - 1 / 4) +
    t₀ * ((κ 1 : ℝ) * χ)]
  let velocity : Fin 2 → ℝ := ![(κ 0 : ℝ) * χ, -((κ 1 : ℝ) * χ)]
  let width : Fin 2 → ℝ := ![2 * χ, WY]
  have hvel : ∀ i, |velocity i| ≤ L := by
    intro i; fin_cases i
    · simpa [velocity] using hL0
    · simpa [velocity, abs_neg] using hL1
  have hdw : ∀ i, δ ≤ width i := by
    intro i; fin_cases i
    · simpa [width] using hdZ
    · simpa [width] using hdY
  have hmove : ∀ i, L * δ ≤ width i := by
    intro i; fin_cases i
    · simpa [width] using hmZ
    · simpa [width] using hmY
  have hbox : ∀ p ∈ E, basePt b p ∈ movingBox (t₀ + q / 2) (q / 2) center velocity width := by
    intro p hp
    obtain ⟨hκ, ht, hy, hζp, _⟩ := hE p hp
    have ht01 : p.2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hunit.1], by linarith [ht.2, hunit.2]⟩
    refine ⟨?_, ?_⟩
    · show |p.2 - (t₀ + q / 2)| ≤ q / 2
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    · intro i
      fin_cases i
      · show |b p.1 0 + p.2 * b p.1 3 - ((κ 1 : ℝ) * χ + p.2 * ((κ 0 : ℝ) * χ))| ≤ 2 * χ
        exact label_Z_near hχ hκ ht01
      · show |b p.1 1 + p.2 * b p.1 4 - (((κ 2 : ℝ) * m + 2 * m * (x - w / 2 - 1 / 4) +
          t₀ * ((κ 1 : ℝ) * χ)) + p.2 * -((κ 1 : ℝ) * χ))| ≤ WY
        have hτ : p.2 = t₀ + q * ((p.2 - t₀) / q) := by field_simp; ring
        have hY := label_Y_eq (q := q) hm.ne' hκ ((p.2 - t₀) / q)
        rw [← hτ] at hY
        rw [hY]
        have hb0 := label_b0_near hχ hκ
        have hdef : |b p.1 4 + (κ 1 : ℝ) * χ| ≤ ζ + χ := by
          calc |b p.1 4 + (κ 1 : ℝ) * χ| = |(b p.1 4 + b p.1 0) - (b p.1 0 - (κ 1 : ℝ) * χ)| := by
                ring_nf
            _ ≤ |b p.1 4 + b p.1 0| + |b p.1 0 - (κ 1 : ℝ) * χ| := abs_sub _ _
            _ ≤ ζ + χ := add_le_add hζp hb0
        have hqτ : q * ((p.2 - t₀) / q) = p.2 - t₀ := by field_simp
        have hτ01 : 0 ≤ p.2 - t₀ ∧ p.2 - t₀ ≤ q := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        unfold domY
        rw [hqτ]
        have e : (κ 2 : ℝ) * m + 2 * m * (sliceY b m t₀ p.1 - 1 / 4) - (p.2 - t₀) * ((κ 1 : ℝ) * χ) +
            (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) -
            (((κ 2 : ℝ) * m + 2 * m * (x - w / 2 - 1 / 4) + t₀ * ((κ 1 : ℝ) * χ)) +
              p.2 * -((κ 1 : ℝ) * χ)) =
            2 * m * (sliceY b m t₀ p.1 - (x - w / 2)) + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) := by
          ring
        rw [e]
        have h1 : |2 * m * (sliceY b m t₀ p.1 - (x - w / 2))| ≤ m * w := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * m)]
          have : |sliceY b m t₀ p.1 - (x - w / 2)| ≤ w / 2 := by
            rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
          nlinarith
        have h2 : |(p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ)| ≤ q * (ζ + χ) := by
          rw [abs_mul, abs_of_nonneg hτ01.1]
          exact mul_le_mul hτ01.2 hdef (abs_nonneg _) hq.le
        calc _ ≤ |2 * m * (sliceY b m t₀ p.1 - (x - w / 2))| +
              |(p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ)| := abs_add_le _ _
          _ ≤ m * w + q * (ζ + χ) := add_le_add h1 h2
  -- split the hidden window into two bins
  set S : Set (α × ℝ) := {p | ⌊b p.1 3 / χ⌋ = κ 0} with hSdef
  have hS : MeasurableSet S := measurable_velocityBin hb _ (κ 0)
  have hES : E ⊆ S := fun p hp => by
    have := congrFun (hE p hp).1 0
    show ⌊b p.1 3 / χ⌋ = κ 0
    simpa [slotKey] using this
  let E₁ : Set (α × ℝ) := E ∩ {p | hidden b p ≤ off (basePt b p)}
  let E₂ : Set (α × ℝ) := E ∩ {p | off (basePt b p) ≤ hidden b p}
  have hsplit : E ⊆ E₁ ∪ E₂ := by
    intro p hp
    rcases le_total (hidden b p) (off (basePt b p)) with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  have hcapS : ∀ c j, (μ.restrict S) {p | baseMesh δ (basePt b p) = c ∧ ⌊hidden b p / a⌋ = j} ≤
      ENNReal.ofReal (K * δ ^ 3 * a ^ d) * π {w | ⌊w / χ⌋ = κ 0} := by
    intro c j
    rw [Measure.restrict_apply' hS]
    have hsub : {p : α × ℝ | baseMesh δ (basePt b p) = c ∧ ⌊hidden b p / a⌋ = j} ∩ S =
        {p | baseMesh δ (basePt b p) = c ∧ ⌊hidden b p / a⌋ = j ∧ ⌊b p.1 3 / χ⌋ = κ 0} := by
      ext p
      simp only [mem_inter_iff, mem_setOf_eq, hSdef]
      tauto
    rw [hsub]
    refine (hcap c j (κ 0)).trans (le_of_eq ?_)
    rw [rpow_cap_split hN]
    congr 2
    ring
  have hone : ∀ (E' : Set (α × ℝ)) (offk : (Fin 3 → ℝ) → ℝ), E' ⊆ E →
      (∀ p ∈ E', ∀ y : Fin 3 → ℝ, (∀ i, |basePt b p i - y i| ≤ δ) →
        |offk (basePt b p) - offk y| ≤ a) →
      (∀ p ∈ E', offk (basePt b p) ≤ hidden b p ∧ hidden b p ≤ offk (basePt b p) + a) →
      μ E' ≤ ENNReal.ofReal (6000 * K * (q / 2) * (2 * χ) * WY * a ^ d) *
        π {w | ⌊w / χ⌋ = κ 0} := by
    intro E' offk hE' hok hwin
    have hE'S : E' ⊆ S := hE'.trans hES
    have hrestr : μ E' = μ.restrict S E' := by
      rw [Measure.restrict_apply' hS, inter_eq_left.mpr hE'S]
    rw [hrestr]
    have hmain := moving_box_signal_cap (μ.restrict S) (basePt b) (hidden b) offk E'
      (δ := δ) (a := a) (θ := a) (radius := q / 2) (L := L) (C := K) (d := d)
      hδ ha ha.le le_rfl hdr hL hK (t₀ + q / 2) center velocity width hvel hdw hmove hok
      (fun p hp => ⟨hbox p (hE' hp), hwin p hp⟩) _ hcapS
    refine hmain.trans (le_of_eq ?_)
    congr 2
  have h1 := hone E₁ (fun y => off y - a) (fun p hp => hp.1)
    (fun p hp y hy => by
      have := ho p hp.1 y hy
      calc |off (basePt b p) - a - (off y - a)| = |off (basePt b p) - off y| := by ring_nf
        _ ≤ a := this)
    (fun p hp => by
      have hw := (hE p hp.1).2.2.2.2
      rw [abs_le] at hw
      have h2' : hidden b p ≤ off (basePt b p) := hp.2
      exact ⟨by linarith [hw.1], by linarith⟩)
  have h2 := hone E₂ off (fun p hp => hp.1) (fun p hp y hy => ho p hp.1 y hy)
    (fun p hp => by
      have hw := (hE p hp.1).2.2.2.2
      rw [abs_le] at hw
      exact ⟨hp.2, by linarith [hw.2]⟩)
  calc μ E ≤ μ (E₁ ∪ E₂) := measure_mono hsplit
    _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (6000 * K * (q / 2) * (2 * χ) * WY * a ^ d) * π {w | ⌊w / χ⌋ = κ 0} +
        ENNReal.ofReal (6000 * K * (q / 2) * (2 * χ) * WY * a ^ d) * π {w | ⌊w / χ⌋ = κ 0} :=
      add_le_add h1 h2
    _ = ENNReal.ofReal (12000 * K * q * χ * WY * a ^ d) * π {w | ⌊w / χ⌋ = κ 0} := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
