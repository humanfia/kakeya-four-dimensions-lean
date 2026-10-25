/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit cc531a6d5d2ca6353cb4bccf36dd4456c84a3879, file Submission/Obl/k4_horizontal_wide_interval_return/Native/KeyJet.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.LabelGraph

set_option autoImplicit false

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-!
# Jet counts over a slot key

Disjoint heavy entries of one slot key whose events follow normalized key graphs
`a · quad2 (F i)` within `a M`, with every `F i` within `M` of one reference `rr`, are counted by
the joint cap (`key_jet_count`).  Their union carries at least `#J · T / K₁`; it is charged by
`key_window_cap` over the full slice range (`key_window_cap_full`):
* when `18 a M ≤ 1`, at the hidden resolution `N^(-s'') = 18 a M` with the moving offset
  `a · quad2 rr` read in key coordinates (`key_jet_fine`);
* when `18 a M > 1`, at the hidden resolution `1` with `⌈Xb⌉₊ + 1 ≤ 2 Xb + 2` constant windows
  covering `|hidden| ≤ Xb` (`key_jet_coarse`); this regime uses the cap at `s' = 0`, whence the
  hypothesis `0 ≤ Rc` of `key_jet_count`.
-/

omit [MeasurableSpace α] in
/-- The slice coordinate of a label of key `κ` in closed form. -/
theorem sliceY_eq_of_key {b : α → Fin 6 → ℝ} {χ m t₀ : ℝ} {l : α} {κ : Fin 3 → ℤ}
    (hκ : slotKey b χ m t₀ l = κ) :
    sliceY b m t₀ l = ((b l 1 + t₀ * b l 4) / m - (κ 2 : ℝ)) / 2 + 1 / 4 := by
  have h2 : ⌊(b l 1 + t₀ * b l 4) / m⌋ = κ 2 := by
    have := congrFun hκ 2; simpa [slotKey] using this
  unfold sliceY
  rw [← Int.self_sub_floor, h2]

omit [MeasurableSpace α] in
/-- Inverting the key's transverse motion at a base point of a key label recovers its slice
coordinate, up to the transverse velocity defect. -/
theorem keyEta_basePt {b : α → Fin 6 → ℝ} {χ m t₀ : ℝ} (hm : m ≠ 0) {p : α × ℝ}
    {κ : Fin 3 → ℤ} (hκ : slotKey b χ m t₀ p.1 = κ) :
    (basePt b p 2 + (basePt b p 0 - t₀) * ((κ 1 : ℝ) * χ) - (κ 2 : ℝ) * m) / (2 * m) + 1 / 4 =
      sliceY b m t₀ p.1 + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m) := by
  rw [sliceY_eq_of_key hκ]
  show (b p.1 1 + p.2 * b p.1 4 + (p.2 - t₀) * ((κ 1 : ℝ) * χ) - (κ 2 : ℝ) * m) / (2 * m) +
    1 / 4 = _
  field_simp
  ring

/-- `key_window_cap` over the full slice range `[1/4, 3/4]`. -/
theorem key_window_cap_full {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v') (κ : Fin 3 → ℤ) {t₀ q m ζ L : ℝ}
    (off : (Fin 3 → ℝ) → ℝ) (E : Set (α × ℝ))
    (hq : 0 < q) (hm : 0 < m) (hζ : 0 ≤ ζ) (hL : 0 ≤ L)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ L) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ L)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m / 2)
    (hmZ : L * N ^ (-r) ≤ 2 * N ^ (-v')) (hmY : L * N ^ (-r) ≤ m / 2)
    (hsmall : q * (ζ + N ^ (-v')) ≤ m / 2)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePt b p i - y i| ≤ N ^ (-r)) →
      |off (basePt b p) - off y| ≤ N ^ (-s'))
    (hE : ∀ p ∈ E, slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      |b p.1 4 + b p.1 0| ≤ ζ ∧ |hidden b p - off (basePt b p)| ≤ N ^ (-s')) :
    μ E ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m * (N ^ (-s')) ^ d) *
      π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  have hχ : 0 < N ^ (-v') := Real.rpow_pos_of_pos hN _
  have hqζ : 0 ≤ q * (ζ + N ^ (-v')) := by positivity
  refine (key_window_cap hb hN hK hcap κ (x := 3 / 4) (w := 1 / 2) off E hq hm (by norm_num)
    hζ hL hunit hL0 hL1 hdr hdZ (by linarith) hmZ (by linarith) ho ?_).trans ?_
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hE p hp
    refine ⟨h1, h2, ?_, h3, h4⟩
    have e : (3 / 4 : ℝ) - 1 / 2 = 1 / 4 := by norm_num
    rw [e]
    exact sliceY_mem b m t₀ p.1
  · have hw : m * (1 / 2) + q * (ζ + N ^ (-v')) ≤ m := by linarith
    gcongr

/-- **Fine regime.** Events of one key, during the slot, whose hidden values follow
`a · quad2 G` (in key coordinates) within `a M` for some `G` within `M` of `rr`, are charged at
the hidden resolution `N^(-s') ≥ 8 a M` with the moving offset `a · quad2 rr`. -/
theorem key_jet_fine {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v') (κ : Fin 3 → ℤ) {t₀ q m ζ Lv a B M : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv) (ha : 0 < a) (hM : 0 < M)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m / 2) (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v'))
    (hmY : Lv * N ^ (-r) ≤ m / 2)
    (hsmall : q * (ζ + N ^ (-v')) ≤ m / 2)
    (hs' : 8 * a * M ≤ N ^ (-s'))
    (rr : Fin 6 → ℝ) (hB : ∀ e, |rr e| ≤ B)
    (hvar : (B + M) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ M)
    (hdrift : (B + M) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ M)
    (S : Set (α × ℝ))
    (hS : ∀ p ∈ S, slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      |b p.1 4 + b p.1 0| ≤ ζ ∧ ∃ G : Fin 6 → ℝ, (∀ e, |G e - rr e| ≤ M) ∧
      |hidden b p - a * quad2 G ((p.2 - t₀) / q) (sliceY b m t₀ p.1)| ≤ a * M) :
    μ S ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m * (N ^ (-s')) ^ d) *
      π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  set χ := N ^ (-v') with hχdef
  set δ := N ^ (-r) with hδdef
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h2m : (0 : ℝ) < 2 * m := by positivity
  -- the slice coordinate read off a base point through the key motion
  set yinv : (Fin 3 → ℝ) → ℝ := fun y =>
    (y 2 + (y 0 - t₀) * ((κ 1 : ℝ) * χ) - (κ 2 : ℝ) * m) / (2 * m) + 1 / 4 with hyinv
  have hη₁ : ∀ p ∈ S, yinv (basePt b p) =
      sliceY b m t₀ p.1 + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m) :=
    fun p hp => keyEta_basePt hm.ne' (hS p hp).1
  have hdrift' : ∀ p ∈ S,
      |(p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)| ≤ q * (ζ + χ) / (2 * m) := by
    intro p hp
    obtain ⟨hκ, ht, hζp, -⟩ := hS p hp
    have hd := key_velocity_defect hχ hκ hζp
    rw [abs_div, abs_mul, abs_of_pos h2m, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ p.2 - t₀)]
    gcongr
    linarith [ht.2]
  have hqm : q * (ζ + χ) / (2 * m) ≤ 1 / 4 := by
    rw [div_le_iff₀ h2m]; linarith
  have hτ₁ : ∀ p ∈ S, |(p.2 - t₀) / q| ≤ 1 := by
    intro p hp
    have ht := (hS p hp).2.1
    rw [abs_le, le_div_iff₀ hq, div_le_iff₀ hq]
    constructor <;> linarith [ht.1, ht.2]
  have hsY : ∀ p ∈ S, |sliceY b m t₀ p.1| ≤ 1 := by
    intro p _
    have h := sliceY_mem b m t₀ p.1
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hη₁b : ∀ p ∈ S, |yinv (basePt b p)| ≤ 1 := by
    intro p hp
    rw [hη₁ p hp]
    have hs := sliceY_mem b m t₀ p.1
    have hd := hdrift' p hp
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hs.1, hs.2, hd.1, hd.2]
  refine key_window_cap_full hb hN hK hcap κ
    (fun y => a * quad2 rr ((y 0 - t₀) / q) (yinv y)) S hq hm hζ hLv hunit hL0 hL1 hdr hdZ
    hdY hmZ hmY hsmall ?_ ?_
  · intro p hp y hy
    have hp0 : basePt b p 0 = p.2 := rfl
    have hτd : |(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| ≤ δ / q := by
      rw [div_sub_div_same, sub_sub_sub_cancel_right, abs_div, abs_of_pos hq]
      exact div_le_div_of_nonneg_right (hy 0) hq.le
    have hδq : δ / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
    have hτ₁' : |(basePt b p 0 - t₀) / q| ≤ 1 := by rw [hp0]; exact hτ₁ p hp
    have hτ₂ : |(y 0 - t₀) / q| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub ((basePt b p 0 - t₀) / q) ((y 0 - t₀) / q)
      have h' := abs_sub_abs_le_abs_sub ((y 0 - t₀) / q) ((basePt b p 0 - t₀) / q)
      rw [abs_sub_comm] at h'
      linarith
    have hηd : |yinv (basePt b p) - yinv y| ≤ (1 + Lv) * δ / (2 * m) := by
      have e : yinv (basePt b p) - yinv y =
          ((basePt b p 2 - y 2) + (basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)) / (2 * m) := by
        simp only [hyinv]
        field_simp
        ring
      rw [e, abs_div, abs_of_pos h2m]
      apply div_le_div_of_nonneg_right _ h2m.le
      calc |(basePt b p 2 - y 2) + (basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)|
          ≤ |basePt b p 2 - y 2| + |(basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)| := abs_add_le _ _
        _ = |basePt b p 2 - y 2| + |basePt b p 0 - y 0| * |(κ 1 : ℝ) * χ| := by rw [abs_mul]
        _ ≤ δ + δ * Lv := by
            gcongr
            · exact hy 2
            · exact hy 0
        _ = (1 + Lv) * δ := by ring
    have hηd' : (1 + Lv) * δ / (2 * m) ≤ 1 / 2 := by
      rw [div_le_iff₀ h2m]; linarith
    have hη₂ : |yinv y| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub (yinv y) (yinv (basePt b p))
      rw [abs_sub_comm] at this
      linarith [hη₁b p hp]
    have hlip := quad2_lipschitz (L := 2) hB (by linarith : |(basePt b p 0 - t₀) / q| ≤ 2) hτ₂
      (by linarith [hη₁b p hp] : |yinv (basePt b p)| ≤ 2) hη₂
    show |a * quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p)) -
      a * quad2 rr ((y 0 - t₀) / q) (yinv y)| ≤ N ^ (-s')
    rw [← mul_sub, abs_mul, abs_of_pos ha]
    have hvar' : B * (1 + 3 * 2) * (|(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| +
        |yinv (basePt b p) - yinv y|) ≤ M := by
      calc B * (1 + 3 * 2) * (|(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| +
            |yinv (basePt b p) - yinv y|)
          ≤ (B + M) * 7 * (δ / q + (1 + Lv) * δ / (2 * m)) := by
            have : B ≤ B + M := by linarith
            gcongr
            norm_num
        _ ≤ M := hvar
    calc a * |quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p)) -
          quad2 rr ((y 0 - t₀) / q) (yinv y)| ≤ a * M :=
          mul_le_mul_of_nonneg_left (hlip.trans hvar') ha.le
      _ ≤ 8 * a * M := by nlinarith
      _ ≤ N ^ (-s') := hs'
  · intro p hp
    obtain ⟨hκ, ht, hζp, G, hG, hfit⟩ := hS p hp
    refine ⟨hκ, ht, hζp, ?_⟩
    have hp0 : basePt b p 0 = p.2 := rfl
    show |hidden b p - a * quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p))| ≤ N ^ (-s')
    rw [hp0]
    set τ := (p.2 - t₀) / q with hτdef
    set sY := sliceY b m t₀ p.1 with hsYdef
    have h1 : |quad2 G τ sY - quad2 rr τ sY| ≤ 6 * M := by
      rw [quad2_sub]
      exact abs_quad2_le (fun e => by simpa [Pi.sub_apply] using hG e) (hτ₁ p hp) (hsY p hp)
    have h2 : |quad2 rr τ sY - quad2 rr τ (yinv (basePt b p))| ≤ M := by
      have hlip := quad2_lipschitz (L := 2) hB (t := τ) (t' := τ) (η := sY)
        (η' := yinv (basePt b p)) (by linarith [hτ₁ p hp]) (by linarith [hτ₁ p hp])
        (by linarith [hsY p hp]) (by linarith [hη₁b p hp])
      have hd : |sY - yinv (basePt b p)| ≤ q * (ζ + χ) / (2 * m) := by
        rw [hη₁ p hp,
          show sY - (sY + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)) =
            -((p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)) by ring, abs_neg]
        exact hdrift' p hp
      rw [sub_self, abs_zero, zero_add] at hlip
      refine hlip.trans ?_
      calc B * (1 + 3 * 2) * |sY - yinv (basePt b p)|
          ≤ (B + M) * 7 * (q * (ζ + χ) / (2 * m)) := by
            have : B ≤ B + M := by linarith
            gcongr
            norm_num
        _ ≤ M := hdrift
    have e : hidden b p - a * quad2 rr τ (yinv (basePt b p)) =
        (hidden b p - a * quad2 G τ sY) + a * (quad2 G τ sY - quad2 rr τ sY) +
          a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p))) := by ring
    rw [e]
    calc _ ≤ |(hidden b p - a * quad2 G τ sY) + a * (quad2 G τ sY - quad2 rr τ sY)| +
          |a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p)))| := abs_add_le _ _
      _ ≤ |hidden b p - a * quad2 G τ sY| + |a * (quad2 G τ sY - quad2 rr τ sY)| +
          |a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p)))| := by
          gcongr; exact abs_add_le _ _
      _ ≤ a * M + a * (6 * M) + a * M := by
          rw [abs_mul, abs_mul, abs_of_pos ha]
          gcongr
      _ = 8 * a * M := by ring
      _ ≤ N ^ (-s') := hs'

/-- **Coarse regime.** Events of one key, during the slot, with hidden values in `[-Xb, Xb]`
are covered by `⌈Xb⌉₊ + 1 ≤ 2 Xb + 2` constant hidden windows of width one, each charged at
the hidden resolution `N^(-0) = 1`. -/
theorem key_jet_coarse {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r 0 v') (κ : Fin 3 → ℤ) {t₀ q m ζ Lv Xb : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv) (hXb : 0 ≤ Xb)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m / 2) (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v'))
    (hmY : Lv * N ^ (-r) ≤ m / 2)
    (hsmall : q * (ζ + N ^ (-v')) ≤ m / 2)
    (S : Set (α × ℝ))
    (hS : ∀ p ∈ S, slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      |b p.1 4 + b p.1 0| ≤ ζ ∧ |hidden b p| ≤ Xb) :
    μ S ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m * (2 * Xb + 2)) *
      π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  have hχ : 0 < N ^ (-v') := Real.rpow_pos_of_pos hN _
  have hone : N ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
  set n : ℕ := ⌈Xb⌉₊ + 1 with hndef
  set c : ℕ → ℝ := fun j => -Xb + 1 + 2 * (j : ℝ) with hcdef
  set Ej : ℕ → Set (α × ℝ) := fun j => S ∩ {p | |hidden b p - c j| ≤ 1} with hEjdef
  have hcover : S ⊆ ⋃ j ∈ Finset.range n, Ej j := by
    intro p hp
    have hX := (hS p hp).2.2.2
    rw [abs_le] at hX
    have h0 : 0 ≤ (hidden b p + Xb) / 2 := by linarith [hX.1]
    have hj1 := Nat.floor_le h0
    have hj2 := Nat.lt_floor_add_one ((hidden b p + Xb) / 2)
    have hceil := Nat.le_ceil Xb
    simp only [mem_iUnion, Finset.mem_range]
    refine ⟨⌊(hidden b p + Xb) / 2⌋₊, ?_, hp, ?_⟩
    · have : (⌊(hidden b p + Xb) / 2⌋₊ : ℝ) < (⌈Xb⌉₊ : ℝ) + 1 := by linarith [hX.2]
      rw [hndef]
      exact_mod_cast this
    · show |hidden b p - (-Xb + 1 + 2 * (⌊(hidden b p + Xb) / 2⌋₊ : ℝ))| ≤ 1
      rw [abs_le]; constructor <;> linarith
  have hEj : ∀ j, μ (Ej j) ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m) *
      π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
    intro j
    have h := key_window_cap_full hb hN hK hcap κ (fun _ => c j) (Ej j) hq hm hζ hLv hunit
      hL0 hL1 hdr hdZ hdY hmZ hmY hsmall
      (fun p _ y _ => by rw [hone, sub_self, abs_zero]; exact zero_le_one)
      (fun p hp => by
        obtain ⟨h1, h2, h3, _⟩ := hS p hp.1
        have h5 : |hidden b p - c j| ≤ 1 := hp.2
        exact ⟨h1, h2, h3, by rw [hone]; exact h5⟩)
    rw [hone, Real.one_rpow, mul_one] at h
    exact h
  calc μ S ≤ μ (⋃ j ∈ Finset.range n, Ej j) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range n, μ (Ej j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (12000 * K * q * N ^ (-v') * m) *
          π {w | ⌊w / N ^ (-v')⌋ = κ 0} := Finset.sum_le_sum (fun j _ => hEj j)
    _ = ENNReal.ofReal ((n : ℝ) * (12000 * K * q * N ^ (-v') * m)) *
          π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m * (2 * Xb + 2)) *
          π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
        gcongr ENNReal.ofReal ?_ * _
        have hn : (n : ℝ) ≤ 2 * Xb + 2 := by
          have := Nat.ceil_lt_add_one hXb
          rw [hndef]; push_cast; linarith
        have h0 : 0 ≤ 12000 * K * q * N ^ (-v') * m := by positivity
        nlinarith

/-- **Jet count over a slot key.** Disjoint heavy entries of one key whose events follow
graphs within `M` of `r` are counted by the joint cap. -/
theorem key_jet_count {μ ρs : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (hρμ : ρs ≤ μ) {N K d r v' Rc : ℝ} (hN : 1 < N) (hK : 0 ≤ K)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc → JointCapAt μ π b N K d r s' v')
    (κ : Fin 3 → ℤ) {t₀ q m ζ Lv a Xb K₁ T B M : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv) (ha : 0 < a) (hK₁ : 0 < K₁)
    (hXb : 0 ≤ Xb) (hM : 0 < M)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m / 2) (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v'))
    (hmY : Lv * N ^ (-r) ≤ m / 2)
    (hsmall : q * (ζ + N ^ (-v')) ≤ m / 2)
    (hT : T = q * N ^ (-v') * m * a ^ d * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal)
    (hTpos : 0 < T) (hπfin : π {w | ⌊w / N ^ (-v')⌋ = κ 0} ≠ ⊤)
    {ι : Type*} (J : Finset ι) (E : ι → Set (α × ℝ)) (F : ι → Fin 6 → ℝ) (rr : Fin 6 → ℝ)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (E i) (E j))
    (hfloor : ∀ i ∈ J, ENNReal.ofReal (T / K₁) ≤ ρs (E i))
    (hnull : ρs (horizSet b ζ)ᶜ = 0)
    (hin : ∀ i ∈ J, ∀ p ∈ E i, p ∈ horizSet b ζ →
      slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧ |hidden b p| ≤ Xb ∧
      |hidden b p - a * quad2 (F i) ((p.2 - t₀) / q) (sliceY b m t₀ p.1)| ≤ a * M)
    (hFr : ∀ i ∈ J, ∀ e, |F i e - rr e| ≤ M) (hB : ∀ e, |rr e| ≤ B)
    (hvar : (B + M) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ M)
    (hdrift : (B + M) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ M)
    (hRc : -Real.logb N (18 * a * M) ≤ Rc) (hRc0 : 0 ≤ Rc) :
    (J.card : ℝ) ≤ K₁ * 12000 * K * (2 * Xb + 2) * (18 * M) ^ d := by
  have hN0 : 0 < N := by linarith
  have hχ : 0 < N ^ (-v') := Real.rpow_pos_of_pos hN0 _
  set P := π {w | ⌊w / N ^ (-v')⌋ = κ 0} with hPdef
  set U := ⋃ i ∈ J, E i with hUdef
  set S := U ∩ horizSet b ζ with hSdef
  -- the heavy entries fill the horizontal part of their union
  have hcount : (J.card : ENNReal) * ENNReal.ofReal (T / K₁) ≤ μ S := by
    have h1 : ρs U = ∑ i ∈ J, ρs (E i) :=
      measure_biUnion_finset (fun i hi j hj hij => hdisj i hi j hj hij) (fun i _ => hE i)
    have h2 : ∑ _i ∈ J, ENNReal.ofReal (T / K₁) ≤ ∑ i ∈ J, ρs (E i) := Finset.sum_le_sum hfloor
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : ρs U ≤ ρs S := by
      calc ρs U ≤ ρs (S ∪ (horizSet b ζ)ᶜ) := measure_mono (fun p hp => by
            by_cases h : p ∈ horizSet b ζ
            · exact Or.inl ⟨hp, h⟩
            · exact Or.inr h)
        _ ≤ ρs S + ρs (horizSet b ζ)ᶜ := measure_union_le _ _
        _ = ρs S := by rw [hnull, add_zero]
    calc (J.card : ENNReal) * ENNReal.ofReal (T / K₁) ≤ ∑ i ∈ J, ρs (E i) := h2
      _ = ρs U := h1.symm
      _ ≤ ρs S := h3
      _ ≤ μ S := hρμ S
  have hSin : ∀ p ∈ S, ∃ i ∈ J, p ∈ E i ∧ p ∈ horizSet b ζ := by
    rintro p ⟨hpU, hph⟩
    rw [hUdef, mem_iUnion₂] at hpU
    obtain ⟨i, hi, hpi⟩ := hpU
    exact ⟨i, hi, hpi, hph⟩
  -- the cap of the horizontal part
  have hbound : μ S ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * m * (2 * Xb + 2) *
      (a ^ d * (18 * M) ^ d)) * P := by
    have h18M : 0 ≤ 18 * M := by positivity
    rcases le_or_gt (18 * a * M) 1 with hfine | hcoarse
    · have h18 : 0 < 18 * a * M := by positivity
      set s'' := -Real.logb N (18 * a * M) with hs''
      have hNs : N ^ (-s'') = 18 * a * M := by
        rw [hs'', neg_neg]; exact Real.rpow_logb hN0 hN.ne' h18
      have hs0 : 0 ≤ s'' := by
        rw [hs'', neg_nonneg]; exact Real.logb_nonpos hN h18.le hfine
      have h := key_jet_fine hb hN0 hK (hcap s'' hs0 hRc) κ hq hm hζ hLv ha hM hunit hL0 hL1
        hdr hdZ hdY hmZ hmY hsmall (by rw [hNs]; nlinarith) rr hB hvar hdrift S
        (fun p hp => by
          obtain ⟨i, hi, hpi, hph⟩ := hSin p hp
          obtain ⟨hκ, ht, _, hfit⟩ := hin i hi p hpi hph
          exact ⟨hκ, ht, hph, F i, hFr i hi, hfit⟩)
      rw [hNs] at h
      refine h.trans ?_
      gcongr ENNReal.ofReal ?_ * _
      rw [show 18 * a * M = a * (18 * M) by ring, Real.mul_rpow ha.le h18M]
      have h0 : 0 ≤ 12000 * K * q * N ^ (-v') * m * (a ^ d * (18 * M) ^ d) := by positivity
      nlinarith
    · have h := key_jet_coarse hb hN0 hK (hcap 0 le_rfl hRc0) κ hq hm hζ hLv hXb hunit hL0 hL1
        hdr hdZ hdY hmZ hmY hsmall S
        (fun p hp => by
          obtain ⟨i, hi, hpi, hph⟩ := hSin p hp
          obtain ⟨hκ, ht, hX, _⟩ := hin i hi p hpi hph
          exact ⟨hκ, ht, hph, hX⟩)
      refine h.trans ?_
      gcongr ENNReal.ofReal ?_ * _
      have h1 : 1 ≤ a ^ d * (18 * M) ^ d := by
        rw [← Real.mul_rpow ha.le h18M]
        exact Real.one_le_rpow (by linarith) hd0
      have h0 : 0 ≤ 12000 * K * q * N ^ (-v') * m * (2 * Xb + 2) := by positivity
      nlinarith
  -- back to real numbers
  have hreal : (J.card : ℝ) * (T / K₁) ≤ 12000 * K * q * N ^ (-v') * m * (2 * Xb + 2) *
      (a ^ d * (18 * M) ^ d) * P.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hπfin)
      (hcount.trans hbound)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (div_pos hTpos hK₁).le, ENNReal.toReal_ofReal (by positivity)] at h
  have hT' : 12000 * K * q * N ^ (-v') * m * (2 * Xb + 2) * (a ^ d * (18 * M) ^ d) * P.toReal =
      12000 * K * (2 * Xb + 2) * (18 * M) ^ d * T := by
    rw [hT]; ring
  rw [hT'] at hreal
  have hdiv : (J.card : ℝ) / K₁ ≤ 12000 * K * (2 * Xb + 2) * (18 * M) ^ d := by
    refine le_of_mul_le_mul_right ?_ hTpos
    calc (J.card : ℝ) / K₁ * T = (J.card : ℝ) * (T / K₁) := by ring
      _ ≤ _ := hreal
  rw [div_le_iff₀ hK₁] at hdiv
  linarith

/-- **Sub-slice graph cap.** The variant of `key_jet_fine` over a slice subinterval
`[x - w, x]`: events of one key, during the slot, with slice coordinate in `[x - w, x]`, whose
hidden values follow `a · quad2 G` (in key coordinates) within `a M` for some `G` within `M` of
`rr`, are charged by `key_window_cap` at the hidden resolution `N^(-s') ≥ 8 a M` with the moving
offset `a · quad2 rr`. -/
theorem key_slice_graph_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v') (κ : Fin 3 → ℤ) {t₀ q m x w ζ Lv a B M : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hw : 0 ≤ w) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv) (ha : 0 < a)
    (hM : 0 < M)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v'))) (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v'))
    (hmY : Lv * N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (hsmall : q * (ζ + N ^ (-v')) ≤ m / 2)
    (hs' : 8 * a * M ≤ N ^ (-s'))
    (rr : Fin 6 → ℝ) (hB : ∀ e, |rr e| ≤ B)
    (hvar : (B + M) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ M)
    (hdrift : (B + M) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ M)
    (S : Set (α × ℝ))
    (hS : ∀ p ∈ S, slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      sliceY b m t₀ p.1 ∈ Icc (x - w) x ∧
      |b p.1 4 + b p.1 0| ≤ ζ ∧ ∃ G : Fin 6 → ℝ, (∀ e, |G e - rr e| ≤ M) ∧
      |hidden b p - a * quad2 G ((p.2 - t₀) / q) (sliceY b m t₀ p.1)| ≤ a * M) :
    μ S ≤ ENNReal.ofReal (12000 * K * q * N ^ (-v') * (m * w + q * (ζ + N ^ (-v'))) *
      (N ^ (-s')) ^ d) * π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  set χ := N ^ (-v') with hχdef
  set δ := N ^ (-r) with hδdef
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h2m : (0 : ℝ) < 2 * m := by positivity
  -- the slice coordinate read off a base point through the key motion
  set yinv : (Fin 3 → ℝ) → ℝ := fun y =>
    (y 2 + (y 0 - t₀) * ((κ 1 : ℝ) * χ) - (κ 2 : ℝ) * m) / (2 * m) + 1 / 4 with hyinv
  have hη₁ : ∀ p ∈ S, yinv (basePt b p) =
      sliceY b m t₀ p.1 + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m) :=
    fun p hp => keyEta_basePt hm.ne' (hS p hp).1
  have hdrift' : ∀ p ∈ S,
      |(p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)| ≤ q * (ζ + χ) / (2 * m) := by
    intro p hp
    obtain ⟨hκ, ht, -, hζp, -⟩ := hS p hp
    have hd := key_velocity_defect hχ hκ hζp
    rw [abs_div, abs_mul, abs_of_pos h2m, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ p.2 - t₀)]
    gcongr
    linarith [ht.2]
  have hqm : q * (ζ + χ) / (2 * m) ≤ 1 / 4 := by
    rw [div_le_iff₀ h2m]; linarith
  have hτ₁ : ∀ p ∈ S, |(p.2 - t₀) / q| ≤ 1 := by
    intro p hp
    have ht := (hS p hp).2.1
    rw [abs_le, le_div_iff₀ hq, div_le_iff₀ hq]
    constructor <;> linarith [ht.1, ht.2]
  have hsY : ∀ p ∈ S, |sliceY b m t₀ p.1| ≤ 1 := by
    intro p _
    have h := sliceY_mem b m t₀ p.1
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hη₁b : ∀ p ∈ S, |yinv (basePt b p)| ≤ 1 := by
    intro p hp
    rw [hη₁ p hp]
    have hs := sliceY_mem b m t₀ p.1
    have hd := hdrift' p hp
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hs.1, hs.2, hd.1, hd.2]
  -- the transverse offset of nearby base points, from the variation budget
  have hηd' : (1 + Lv) * δ / (2 * m) ≤ 1 / 2 := by
    have hA0 : 0 ≤ δ / q := div_nonneg hδ.le hq.le
    have h7 : M * 7 * (δ / q + (1 + Lv) * δ / (2 * m)) ≤ M := by
      refine le_trans ?_ hvar
      have : M ≤ B + M := by linarith
      gcongr
    have key : ∀ A C : ℝ, 0 ≤ A → M * 7 * (A + C) ≤ M → C ≤ 1 / 2 := by
      intro A C hA h
      nlinarith
    exact key _ _ hA0 h7
  refine key_window_cap hb hN hK hcap κ (x := x) (w := w)
    (fun y => a * quad2 rr ((y 0 - t₀) / q) (yinv y)) S hq hm hw hζ hLv hunit hL0 hL1 hdr hdZ
    hdY hmZ hmY ?_ ?_
  · intro p hp y hy
    have hp0 : basePt b p 0 = p.2 := rfl
    have hτd : |(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| ≤ δ / q := by
      rw [div_sub_div_same, sub_sub_sub_cancel_right, abs_div, abs_of_pos hq]
      exact div_le_div_of_nonneg_right (hy 0) hq.le
    have hδq : δ / q ≤ 1 / 2 := by rw [div_le_iff₀ hq]; linarith
    have hτ₁' : |(basePt b p 0 - t₀) / q| ≤ 1 := by rw [hp0]; exact hτ₁ p hp
    have hτ₂ : |(y 0 - t₀) / q| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub ((basePt b p 0 - t₀) / q) ((y 0 - t₀) / q)
      have h' := abs_sub_abs_le_abs_sub ((y 0 - t₀) / q) ((basePt b p 0 - t₀) / q)
      rw [abs_sub_comm] at h'
      linarith
    have hηd : |yinv (basePt b p) - yinv y| ≤ (1 + Lv) * δ / (2 * m) := by
      have e : yinv (basePt b p) - yinv y =
          ((basePt b p 2 - y 2) + (basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)) / (2 * m) := by
        simp only [hyinv]
        field_simp
        ring
      rw [e, abs_div, abs_of_pos h2m]
      apply div_le_div_of_nonneg_right _ h2m.le
      calc |(basePt b p 2 - y 2) + (basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)|
          ≤ |basePt b p 2 - y 2| + |(basePt b p 0 - y 0) * ((κ 1 : ℝ) * χ)| := abs_add_le _ _
        _ = |basePt b p 2 - y 2| + |basePt b p 0 - y 0| * |(κ 1 : ℝ) * χ| := by rw [abs_mul]
        _ ≤ δ + δ * Lv := by
            gcongr
            · exact hy 2
            · exact hy 0
        _ = (1 + Lv) * δ := by ring
    have hη₂ : |yinv y| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub (yinv y) (yinv (basePt b p))
      rw [abs_sub_comm] at this
      linarith [hη₁b p hp]
    have hlip := quad2_lipschitz (L := 2) hB (by linarith : |(basePt b p 0 - t₀) / q| ≤ 2) hτ₂
      (by linarith [hη₁b p hp] : |yinv (basePt b p)| ≤ 2) hη₂
    show |a * quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p)) -
      a * quad2 rr ((y 0 - t₀) / q) (yinv y)| ≤ N ^ (-s')
    rw [← mul_sub, abs_mul, abs_of_pos ha]
    have hvar' : B * (1 + 3 * 2) * (|(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| +
        |yinv (basePt b p) - yinv y|) ≤ M := by
      calc B * (1 + 3 * 2) * (|(basePt b p 0 - t₀) / q - (y 0 - t₀) / q| +
            |yinv (basePt b p) - yinv y|)
          ≤ (B + M) * 7 * (δ / q + (1 + Lv) * δ / (2 * m)) := by
            have : B ≤ B + M := by linarith
            gcongr
            norm_num
        _ ≤ M := hvar
    calc a * |quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p)) -
          quad2 rr ((y 0 - t₀) / q) (yinv y)| ≤ a * M :=
          mul_le_mul_of_nonneg_left (hlip.trans hvar') ha.le
      _ ≤ 8 * a * M := by nlinarith
      _ ≤ N ^ (-s') := hs'
  · intro p hp
    obtain ⟨hκ, ht, hsl, hζp, G, hG, hfit⟩ := hS p hp
    refine ⟨hκ, ht, hsl, hζp, ?_⟩
    have hp0 : basePt b p 0 = p.2 := rfl
    show |hidden b p - a * quad2 rr ((basePt b p 0 - t₀) / q) (yinv (basePt b p))| ≤ N ^ (-s')
    rw [hp0]
    set τ := (p.2 - t₀) / q with hτdef
    set sY := sliceY b m t₀ p.1 with hsYdef
    have h1 : |quad2 G τ sY - quad2 rr τ sY| ≤ 6 * M := by
      rw [quad2_sub]
      exact abs_quad2_le (fun e => by simpa [Pi.sub_apply] using hG e) (hτ₁ p hp) (hsY p hp)
    have h2 : |quad2 rr τ sY - quad2 rr τ (yinv (basePt b p))| ≤ M := by
      have hlip := quad2_lipschitz (L := 2) hB (t := τ) (t' := τ) (η := sY)
        (η' := yinv (basePt b p)) (by linarith [hτ₁ p hp]) (by linarith [hτ₁ p hp])
        (by linarith [hsY p hp]) (by linarith [hη₁b p hp])
      have hd : |sY - yinv (basePt b p)| ≤ q * (ζ + χ) / (2 * m) := by
        rw [hη₁ p hp,
          show sY - (sY + (p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)) =
            -((p.2 - t₀) * (b p.1 4 + (κ 1 : ℝ) * χ) / (2 * m)) by ring, abs_neg]
        exact hdrift' p hp
      rw [sub_self, abs_zero, zero_add] at hlip
      refine hlip.trans ?_
      calc B * (1 + 3 * 2) * |sY - yinv (basePt b p)|
          ≤ (B + M) * 7 * (q * (ζ + χ) / (2 * m)) := by
            have : B ≤ B + M := by linarith
            gcongr
            norm_num
        _ ≤ M := hdrift
    have e : hidden b p - a * quad2 rr τ (yinv (basePt b p)) =
        (hidden b p - a * quad2 G τ sY) + a * (quad2 G τ sY - quad2 rr τ sY) +
          a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p))) := by ring
    rw [e]
    calc _ ≤ |(hidden b p - a * quad2 G τ sY) + a * (quad2 G τ sY - quad2 rr τ sY)| +
          |a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p)))| := abs_add_le _ _
      _ ≤ |hidden b p - a * quad2 G τ sY| + |a * (quad2 G τ sY - quad2 rr τ sY)| +
          |a * (quad2 rr τ sY - quad2 rr τ (yinv (basePt b p)))| := by
          gcongr; exact abs_add_le _ _
      _ ≤ a * M + a * (6 * M) + a * M := by
          rw [abs_mul, abs_mul, abs_of_pos ha]
          gcongr
      _ = 8 * a * M := by ring
      _ ≤ N ^ (-s') := hs'

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
