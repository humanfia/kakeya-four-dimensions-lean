/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit 65c4e2637434d106fc91d7e4dede209e05034e55, file Submission/Obl/k4_horizontal_wide_interval_return/Native/ShortKey.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.KeyJet

set_option autoImplicit false

/-!
# Two label families on one slot key

Two finite families of label sets on one slot key (disjoint within each family), every label
following the normalized key graph of its set within `a W₁` (resp. `a W₂`) during the slot, and
every set heavy (incidence mass at least `T / K₁` during the slot): the incidences of pairs whose
key graphs differ by `Mst` in some coefficient carry at most
`A (Mst/δ)^-η (|ι₁| + |ι₂|) T` (`key_pairs_abstract`).  Interval ceilings come from
`key_slice_graph_cap`, list counts from `key_jet_count`, and the matching from `pair_compare`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Numerics of one slot key. -/
structure KeyNum (N K d r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ B W₁ W₂ δ Mst A w η R₀ : ℝ)
    (κ : Fin 3 → ℤ) : Prop where
  hN : 1 < N
  hK : 0 ≤ K
  hd0 : 0 ≤ d
  hd1 : d < 1
  hRc0 : 0 ≤ Rc
  hs₁0 : 0 ≤ s₁
  hs₁R : s₁ ≤ Rc
  hq : 0 < q
  hm : 0 < m
  hζ : 0 ≤ ζ
  hLv : 0 ≤ Lv
  ha : 0 < a
  hK₁ : 0 < K₁
  hXb : 0 ≤ Xb
  hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1
  hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv
  hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv
  hdr : N ^ (-r) ≤ q / 2
  hdZ : N ^ (-r) ≤ 2 * N ^ (-v')
  hdYw : N ^ (-r) ≤ m * w
  hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v')
  hmYw : Lv * N ^ (-r) ≤ m * w
  hsmall : q * (ζ + N ^ (-v')) ≤ m * w
  hW₁ : 0 < W₁
  hW₂ : 0 < W₂
  hδW : W₁ + W₂ ≤ δ
  hW₁M : W₁ ≤ Mst
  hW₂M : W₂ ≤ Mst
  hR₀ : R₀ * δ ≤ Mst
  hA1 : 1 ≤ A
  hAη : A ≤ (Mst / δ) ^ η
  hw : 0 < w
  hw4 : w ≤ 1 / 4
  hBw : 18 * B * w ≤ δ
  hs₁₁ : 8 * a * W₁ ≤ N ^ (-s₁)
  hs₁₂ : 8 * a * W₂ ≤ N ^ (-s₁)
  hcapw : 12000 * K * (m * w + q * (ζ + N ^ (-v'))) * (N ^ (-s₁)) ^ d ≤ A * m * w * a ^ d
  hvar₁ : (B + W₁) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ W₁
  hvar₂ : (B + W₂) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ W₂
  hdrift₁ : (B + W₁) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ W₁
  hdrift₂ : (B + W₂) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ W₂
  hvarJ : (B + 2 * Mst) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ Mst
  hdriftJ : (B + 2 * Mst) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ Mst
  hRcJ : -Real.logb N (18 * a * Mst) ≤ Rc
  hAjet : K₁ * 12000 * K * (2 * Xb + 2) * 18 * (δ + 1) ≤ A

/-- `(B + 2M) X ≤ M` for all `M ≥ Mst` once it holds at `Mst`. -/
theorem mono_var {B X Mst M : ℝ} (hB : 0 ≤ B) (hX : 0 ≤ X) (hMst : 0 < Mst)
    (h : (B + 2 * Mst) * X ≤ Mst) (hM : Mst ≤ M) : (B + 2 * M) * X ≤ M := by
  have hX2 : 2 * X ≤ 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hB hX]
  nlinarith [mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ 1 - 2 * X), mul_nonneg hB hX]

theorem logb_anti {N a M M' : ℝ} (hN : 1 < N) (ha : 0 < a) (hM : 0 < M) (hMM : M ≤ M') :
    -Real.logb N (18 * a * M') ≤ -Real.logb N (18 * a * M) := by
  apply neg_le_neg
  apply Real.logb_le_logb_of_le hN (by positivity)
  nlinarith

omit [MeasurableSpace α] in
/-- A label hypothesis read at an incidence of the slot, at the normalized time
`(p.2 - t₀) / q`. -/
theorem lab_at {b : α → Fin 6 → ℝ} {χ m t₀ q ζ Xb a W : ℝ} {κ : Fin 3 → ℤ} {C : Set α}
    {F : Fin 6 → ℝ} (hq : 0 < q)
    (hlab : ∀ l ∈ C, |b l 4 + b l 0| ≤ ζ → slotKey b χ m t₀ l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 - a * quad2 F τ (sliceY b m t₀ l)| ≤ a * W)
    {p : α × ℝ} (hp1 : p.1 ∈ C) (hp2 : p.2 ∈ Icc t₀ (t₀ + q)) (hh : p ∈ horizSet b ζ) :
    slotKey b χ m t₀ p.1 = κ ∧ |hidden b p| ≤ Xb ∧
      |hidden b p - a * quad2 F ((p.2 - t₀) / q) (sliceY b m t₀ p.1)| ≤ a * W := by
  obtain ⟨hκ, hτ⟩ := hlab p.1 hp1 hh
  have hmem : (p.2 - t₀) / q ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hp2.1]) hq.le, (div_le_one hq).mpr (by linarith [hp2.2])⟩
  have heq : t₀ + q * ((p.2 - t₀) / q) = p.2 := by
    rw [mul_div_cancel₀ _ hq.ne']
    ring
  obtain ⟨hX, hfit⟩ := hτ _ hmem
  rw [heq] at hX hfit
  exact ⟨hκ, hX, hfit⟩

/-- `c (18 M)^d ≤ A (M/δ)^d` from `c · 18 (δ + 1) ≤ A`, for `0 ≤ d < 1`. -/
theorem jet_num {c d δ M A : ℝ} (hc : 0 ≤ c) (hd0 : 0 ≤ d) (hd1 : d < 1) (hδ : 0 < δ)
    (hM : 0 < M) (hA : c * 18 * (δ + 1) ≤ A) : c * (18 * M) ^ d ≤ A * (M / δ) ^ d := by
  have h18 : (18 : ℝ) ^ d ≤ 18 := Real.rpow_le_self_of_one_le (by norm_num) hd1.le
  have hδd : δ ^ d ≤ δ + 1 := by
    rcases le_or_gt δ 1 with h | h
    · linarith [Real.rpow_le_one hδ.le h hd0]
    · linarith [Real.rpow_le_self_of_one_le h.le hd1.le]
  have hδd0 : 0 < δ ^ d := Real.rpow_pos_of_pos hδ d
  have hMd : 0 ≤ M ^ d := Real.rpow_nonneg hM.le d
  have h18d : 0 ≤ (18 : ℝ) ^ d := Real.rpow_nonneg (by norm_num) d
  have key : c * 18 ^ d * δ ^ d ≤ A := by
    calc c * 18 ^ d * δ ^ d ≤ c * 18 * (δ + 1) := by gcongr
      _ ≤ A := hA
  rw [Real.mul_rpow (by norm_num) hM.le, Real.div_rpow hM.le hδ.le, ← mul_div_assoc,
    le_div_iff₀ hδd0]
  calc c * (18 ^ d * M ^ d) * δ ^ d = c * 18 ^ d * δ ^ d * M ^ d := by ring
    _ ≤ A * M ^ d := mul_le_mul_of_nonneg_right key hMd

/-- **Interval ceiling of one label set on the slot key**, from `key_slice_graph_cap`. -/
theorem slot_ceiling {μ ρs : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (hρμ : ρs ≤ μ)
    {η R₀ d N K r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ T B W₁ W₂ δ Mst A w W : ℝ} {κ : Fin 3 → ℤ}
    (hn : KeyNum N K d r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ B W₁ W₂ δ Mst A w η R₀ κ)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc → JointCapAt μ π b N K d r s' v')
    (hT : T = q * N ^ (-v') * m * a ^ d * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal)
    (hπfin : π {w | ⌊w / N ^ (-v')⌋ = κ 0} ≠ ⊤)
    (hnull : ρs (horizSet b ζ)ᶜ = 0)
    {C : Set α} {F : Fin 6 → ℝ} (hW : 0 < W) (hFB : ∀ e, |F e| ≤ B)
    (hs : 8 * a * W ≤ N ^ (-s₁))
    (hvar : (B + W) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) ≤ W)
    (hdrift : (B + W) * 7 * (q * (ζ + N ^ (-v')) / (2 * m)) ≤ W)
    (hlab : ∀ l ∈ C, |b l 4 + b l 0| ≤ ζ → slotKey b (N ^ (-v')) m t₀ l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 - a * quad2 F τ (sliceY b m t₀ l)| ≤ a * W)
    (x : ℝ) :
    ρs ((C ∩ {l | sliceY b m t₀ l ∈ Icc (x - w) x}) ×ˢ Icc t₀ (t₀ + q)) ≤
      ENNReal.ofReal (A * T * w) := by
  have hN0 : 0 < N := by linarith [hn.hN]
  have hχ : 0 < N ^ (-v') := Real.rpow_pos_of_pos hN0 _
  have hK := hn.hK
  have hq := hn.hq
  have hm := hn.hm
  have hζ := hn.hζ
  have hw := hn.hw
  have hmw : m * w ≤ m / 4 := by nlinarith [hn.hw4]
  have hqζ : 0 ≤ q * (ζ + N ^ (-v')) := by positivity
  have hS : ∀ p ∈ ((C ∩ {l | sliceY b m t₀ l ∈ Icc (x - w) x}) ×ˢ Icc t₀ (t₀ + q)) ∩
      horizSet b ζ,
      slotKey b (N ^ (-v')) m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
      sliceY b m t₀ p.1 ∈ Icc (x - w) x ∧ |b p.1 4 + b p.1 0| ≤ ζ ∧
      ∃ G : Fin 6 → ℝ, (∀ e, |G e - F e| ≤ W) ∧
        |hidden b p - a * quad2 G ((p.2 - t₀) / q) (sliceY b m t₀ p.1)| ≤ a * W := by
    rintro p ⟨⟨⟨hpC, hpY⟩, hpI⟩, hph⟩
    obtain ⟨hκ, -, hfit⟩ := lab_at hq hlab hpC hpI hph
    exact ⟨hκ, hpI, hpY, hph, F, fun e => by simp [hW.le], hfit⟩
  have hcapS := key_slice_graph_cap hb hN0 hK (hcap s₁ hn.hs₁0 hn.hs₁R) κ hq hm hw.le hζ
    hn.hLv hn.ha hW hn.hunit hn.hL0 hn.hL1 hn.hdr hn.hdZ (by linarith [hn.hdYw]) hn.hmZ
    (by linarith [hn.hmYw]) (by linarith [hn.hsmall]) hs F hFB hvar hdrift _ hS
  have hPr : 0 ≤ (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal := ENNReal.toReal_nonneg
  calc ρs ((C ∩ {l | sliceY b m t₀ l ∈ Icc (x - w) x}) ×ˢ Icc t₀ (t₀ + q))
      = ρs (((C ∩ {l | sliceY b m t₀ l ∈ Icc (x - w) x}) ×ˢ Icc t₀ (t₀ + q)) ∩
          horizSet b ζ) := (measure_inter_conull hnull).symm
    _ ≤ μ (((C ∩ {l | sliceY b m t₀ l ∈ Icc (x - w) x}) ×ˢ Icc t₀ (t₀ + q)) ∩
          horizSet b ζ) := hρμ _
    _ ≤ _ := hcapS
    _ ≤ ENNReal.ofReal (A * T * w) := by
        rw [← ENNReal.ofReal_toReal hπfin, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hT]
        calc 12000 * K * q * N ^ (-v') * (m * w + q * (ζ + N ^ (-v'))) * (N ^ (-s₁)) ^ d *
              (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal
            = (12000 * K * (m * w + q * (ζ + N ^ (-v'))) * (N ^ (-s₁)) ^ d) *
              (q * N ^ (-v') * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal) := by ring
          _ ≤ (A * m * w * a ^ d) * (q * N ^ (-v') * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal) :=
            mul_le_mul_of_nonneg_right hn.hcapw (by positivity)
          _ = A * (q * N ^ (-v') * m * a ^ d * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal) * w := by
            ring

/-- **List count of one label family on the slot key**, from `key_jet_count`. -/
theorem slot_count {μ ρs : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (hρμ : ρs ≤ μ)
    {η R₀ d N K r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ T B W₁ W₂ δ Mst A w W : ℝ} {κ : Fin 3 → ℤ}
    (hn : KeyNum N K d r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ B W₁ W₂ δ Mst A w η R₀ κ)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc → JointCapAt μ π b N K d r s' v')
    (hT : T = q * N ^ (-v') * m * a ^ d * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal)
    (hTpos : 0 < T) (hπfin : π {w | ⌊w / N ^ (-v')⌋ = κ 0} ≠ ⊤)
    (hnull : ρs (horizSet b ζ)ᶜ = 0)
    {ι : Type} (C : ι → Set α) (F : ι → Fin 6 → ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (C i) (C i'))
    (hfl : ∀ i, ENNReal.ofReal (T / K₁) ≤ ρs (C i ×ˢ Icc t₀ (t₀ + q)))
    (hWM : W ≤ Mst)
    (hlab : ∀ i, ∀ l ∈ C i, |b l 4 + b l 0| ≤ ζ → slotKey b (N ^ (-v')) m t₀ l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 - a * quad2 (F i) τ (sliceY b m t₀ l)| ≤ a * W)
    (hFB : ∀ i e, |F i e| ≤ B) (r' : Fin 6 → ℝ) (M : ℝ) (hM : Mst ≤ M)
    (J : Finset ι) (hJ : ∀ i ∈ J, ∀ k, |F i k - r' k| ≤ M) :
    (J.card : ℝ) ≤ A * (M / δ) ^ d := by
  have hN0 : 0 < N := by linarith [hn.hN]
  have hχ : 0 < N ^ (-v') := Real.rpow_pos_of_pos hN0 _
  have hr0 : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hq := hn.hq
  have hm := hn.hm
  have hζ := hn.hζ
  have hLv := hn.hLv
  have hMst0 : 0 < Mst := lt_of_lt_of_le hn.hW₁ hn.hW₁M
  have hM0 : 0 < M := lt_of_lt_of_le hMst0 hM
  have hδ : 0 < δ := by linarith [hn.hW₁, hn.hW₂, hn.hδW]
  have hmw : m * w ≤ m / 4 := by nlinarith [hn.hw4]
  rcases J.eq_empty_or_nonempty with hJe | ⟨i₁, hi₁⟩
  · rw [hJe, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by linarith [hn.hA1]) (Real.rpow_nonneg (div_pos hM0 hδ).le d)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB i₁ 0)
  have hr : ∀ e, |r' e| ≤ B + M := by
    intro e
    have h1 := hJ i₁ hi₁ e
    have h2 := hFB i₁ e
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hX1 : 0 ≤ 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m)) := by positivity
  have hX2 : 0 ≤ 7 * (q * (ζ + N ^ (-v')) / (2 * m)) := by positivity
  have hvar := mono_var hB0 hX1 hMst0 (by rw [← mul_assoc]; exact hn.hvarJ) hM
  have hdrift := mono_var hB0 hX2 hMst0 (by rw [← mul_assoc]; exact hn.hdriftJ) hM
  have hcount := key_jet_count hb hρμ hn.hN hn.hK hn.hd0 hn.hd1.le hcap κ hq hm hζ hLv hn.ha
    hn.hK₁ hn.hXb hM0 hn.hunit hn.hL0 hn.hL1 hn.hdr hn.hdZ (by linarith [hn.hdYw]) hn.hmZ
    (by linarith [hn.hmYw]) (by linarith [hn.hsmall]) hT hTpos hπfin J
    (fun i => C i ×ˢ Icc t₀ (t₀ + q)) F r' (fun i => (hC i).prod measurableSet_Icc)
    (fun i _ j _ hij => Set.disjoint_prod.mpr (Or.inl (hdisj i j hij))) (fun i _ => hfl i) hnull
    (fun i _ p hp hh => by
      obtain ⟨hκ, hX, hfit⟩ := lab_at hq (hlab i) hp.1 hp.2 hh
      exact ⟨hκ, hp.2, hX, hfit.trans (mul_le_mul_of_nonneg_left (hWM.trans hM) hn.ha.le)⟩)
    hJ hr
    (by calc (B + M + M) * 7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m))
          = (B + 2 * M) * (7 * (N ^ (-r) / q + (1 + Lv) * N ^ (-r) / (2 * m))) := by ring
        _ ≤ M := hvar)
    (by calc (B + M + M) * 7 * (q * (ζ + N ^ (-v')) / (2 * m))
          = (B + 2 * M) * (7 * (q * (ζ + N ^ (-v')) / (2 * m))) := by ring
        _ ≤ M := hdrift)
    ((logb_anti hn.hN hn.ha hMst0 hM).trans hn.hRcJ) hn.hRc0
  have hc : 0 ≤ K₁ * 12000 * K * (2 * Xb + 2) := by
    have := hn.hK₁; have := hn.hK; have := hn.hXb; positivity
  exact hcount.trans (jet_num hc hn.hd0 hn.hd1 hδ hM0 hn.hAjet)

/-- **Pairs of two label families on one slot key.** -/
theorem key_pairs_abstract {η R₀ d : ℝ}
    (hPC : ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (yf : α → ℝ), Measurable yf →
      ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
        (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α)
        (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
        (δ Mst A B w : ℝ),
        (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
        (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
        (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
        0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
        0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
        (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
        (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
        (∀ i (x : ℝ), ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₁ i * w)) →
        (∀ j (x : ℝ), ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₂ j * w)) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ d) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ d) →
        (∀ i j, ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → yf p.1 ∈ closeSet (F₁ i) (F₂ j) δ) →
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
            ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
          ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)))
    {μ ρs : Measure (α × ℝ)} [IsFiniteMeasure ρs] {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (hρμ : ρs ≤ μ) {N K r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ T B W₁ W₂ δ Mst A w : ℝ}
    {κ : Fin 3 → ℤ}
    (hn : KeyNum N K d r v' Rc s₁ t₀ q m ζ Lv a Xb K₁ B W₁ W₂ δ Mst A w η R₀ κ)
    (hcap : ∀ s', 0 ≤ s' → s' ≤ Rc → JointCapAt μ π b N K d r s' v')
    (hT : T = q * N ^ (-v') * m * a ^ d * (π {w | ⌊w / N ^ (-v')⌋ = κ 0}).toReal)
    (hTpos : 0 < T) (hπfin : π {w | ⌊w / N ^ (-v')⌋ = κ 0} ≠ ⊤)
    (hnull : ρs (horizSet b ζ)ᶜ = 0)
    (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α) (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ)
    (hC₁ : ∀ i, MeasurableSet (C₁ i)) (hC₂ : ∀ j, MeasurableSet (C₂ j))
    (hdisj₁ : ∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i'))
    (hdisj₂ : ∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j'))
    (hfl₁ : ∀ i, ENNReal.ofReal (T / K₁) ≤ ρs (C₁ i ×ˢ Icc t₀ (t₀ + q)))
    (hfl₂ : ∀ j, ENNReal.ofReal (T / K₁) ≤ ρs (C₂ j ×ˢ Icc t₀ (t₀ + q)))
    (hlab₁ : ∀ i, ∀ l ∈ C₁ i, |b l 4 + b l 0| ≤ ζ → slotKey b (N ^ (-v')) m t₀ l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 - a * quad2 (F₁ i) τ (sliceY b m t₀ l)| ≤ a * W₁)
    (hlab₂ : ∀ j, ∀ l ∈ C₂ j, |b l 4 + b l 0| ≤ ζ → slotKey b (N ^ (-v')) m t₀ l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, |b l 2 + (t₀ + q * τ) * b l 5| ≤ Xb ∧
        |b l 2 + (t₀ + q * τ) * b l 5 - a * quad2 (F₂ j) τ (sliceY b m t₀ l)| ≤ a * W₂)
    (hB₁ : ∀ i e, |F₁ i e| ≤ B) (hB₂ : ∀ j e, |F₂ j e| ≤ B) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ e, Mst ≤ |F₁ i e - F₂ j e|),
        ρs ((C₁ i ∩ C₂ j) ×ˢ Icc t₀ (t₀ + q))) ≤
      ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
        ((Fintype.card ι₁ + Fintype.card ι₂ : ℝ) * T)) := by
  classical
  have hδ : 0 < δ := by linarith [hn.hW₁, hn.hW₂, hn.hδW]
  -- the slot-restricted measure
  have hρapply : ∀ X : Set α,
      ρs.restrict (univ ×ˢ Icc t₀ (t₀ + q)) (X ×ˢ univ) = ρs (X ×ˢ Icc t₀ (t₀ + q)) := by
    intro X
    rw [Measure.restrict_apply' (MeasurableSet.univ.prod measurableSet_Icc), prod_inter_prod,
      inter_univ, univ_inter]
  -- closeness of the two graphs at every horizontal incidence
  have hae : ∀ᵐ p ∂ρs, p ∈ horizSet b ζ := mem_ae_iff.mpr hnull
  have hclose : ∀ i j, ∀ᵐ p ∂(ρs.restrict (univ ×ˢ Icc t₀ (t₀ + q))), p.1 ∈ C₁ i →
      p.1 ∈ C₂ j → sliceY b m t₀ p.1 ∈ closeSet (F₁ i) (F₂ j) δ := by
    intro i j
    filter_upwards [ae_restrict_of_ae hae] with p hp h1 h2
    obtain ⟨-, hτ₁⟩ := hlab₁ i p.1 h1 hp
    obtain ⟨-, hτ₂⟩ := hlab₂ j p.1 h2 hp
    refine ⟨sliceY_mem b m t₀ p.1, mem_iInter₂.mpr fun t ht => ?_⟩
    obtain ⟨-, f1⟩ := hτ₁ t ht
    obtain ⟨-, f2⟩ := hτ₂ t ht
    show |quad2 (F₁ i) t (sliceY b m t₀ p.1) - quad2 (F₂ j) t (sliceY b m t₀ p.1)| ≤ δ
    have ha := hn.ha
    have hW := mul_le_mul_of_nonneg_left hn.hδW ha.le
    rw [abs_le] at f1 f2 ⊢
    constructor <;> nlinarith [f1.1, f1.2, f2.1, f2.2]
  have hmain := hPC (ρs.restrict (univ ×ˢ Icc t₀ (t₀ + q))) (sliceY b m t₀)
    (measurable_sliceY hb m t₀) ι₁ ι₂ C₁ C₂ F₁ F₂ (fun _ => T) (fun _ => T) δ Mst A B w
    hC₁ hC₂ hdisj₂ hdisj₁ hδ hn.hR₀ hn.hA1 hn.hAη hn.hw hn.hw4 hn.hBw
    (fun _ => hTpos.le) (fun _ => hTpos.le) hB₁ hB₂
    (fun i x => by
      rw [hρapply]
      exact slot_ceiling hb hρμ hn hcap hT hπfin hnull hn.hW₁ (hB₁ i) hn.hs₁₁ hn.hvar₁
        hn.hdrift₁ (hlab₁ i) x)
    (fun j x => by
      rw [hρapply]
      exact slot_ceiling hb hρμ hn hcap hT hπfin hnull hn.hW₂ (hB₂ j) hn.hs₁₂ hn.hvar₂
        hn.hdrift₂ (hlab₂ j) x)
    (fun r' M hM => slot_count hb hρμ hn hcap hT hTpos hπfin hnull C₁ F₁ hC₁ hdisj₁ hfl₁
      hn.hW₁M hlab₁ hB₁ r' M hM _ (fun i hi => (Finset.mem_filter.mp hi).2))
    (fun r' M hM => slot_count hb hρμ hn hcap hT hTpos hπfin hnull C₂ F₂ hC₂ hdisj₂ hfl₂
      hn.hW₂M hlab₂ hB₂ r' M hM _ (fun j hj => (Finset.mem_filter.mp hj).2))
    hclose
  simp only [hρapply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hmain
  rw [add_mul]
  exact hmain

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
