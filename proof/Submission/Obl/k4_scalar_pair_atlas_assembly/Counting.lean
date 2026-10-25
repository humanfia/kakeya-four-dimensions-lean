import Submission.Obl.k4_scalar_pair_atlas_assembly.Geometry

/-!
# Counting compatible output labels

Output labels are determined by their coarse block, their static frame and their nine-node code.
A witness label is compatible with an output label only when the frame lies in a window of
`8 K + 1` frames around the witness, and the code is within one of the witness code at that
frame (coordinatewise).  This bounds every compatibility list by `(8 K + 1) * 3 ^ 9`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Codes within one of a reference code: at most `3 ^ 9` codes per reference. -/
lemma card_offsets : (Fintype.piFinset (fun _ : Fin 3 =>
    Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1))).card = 3 ^ 9 := by
  simp [Fintype.card_piFinset]

/-- Abstract counting: labels in `S` are determined by (block, frame, code); each label has its
block in `Bs`, its frame in `Ds`, and its code within one of the reference code of some witness
in `Ws`. -/
theorem card_le_of_near_codes {ι β κ : Type*} [DecidableEq β] [DecidableEq κ]
    (S : Finset ι) (Bs : Finset β) (Ds : Finset ℤ) (Ws : Finset κ)
    (blk : ι → β) (frm : ι → ℤ) (cd : ι → Fin 3 → Fin 3 → ℤ)
    (ref : κ → β → ℤ → Fin 3 → Fin 3 → ℤ)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, blk s = blk s' → frm s = frm s' → cd s = cd s' → s = s')
    (hS : ∀ s ∈ S, blk s ∈ Bs ∧ frm s ∈ Ds ∧
      ∃ w ∈ Ws, ∀ m m', |cd s m m' - ref w (blk s) (frm s) m m'| ≤ 1) :
    S.card ≤ Bs.card * Ds.card * Ws.card * 3 ^ 9 := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨s₀, hs₀⟩
  · simp [hSe]
  obtain ⟨w₀, -, -⟩ := (hS s₀ hs₀).2.2
  have : Nonempty κ := ⟨w₀⟩
  have hw : ∀ s, ∃ w : κ, s ∈ S → w ∈ Ws ∧
      ∀ m m', |cd s m m' - ref w (blk s) (frm s) m m'| ≤ 1 := by
    intro s
    by_cases h : s ∈ S
    · obtain ⟨w, hw, hc⟩ := (hS s h).2.2
      exact ⟨w, fun _ => ⟨hw, hc⟩⟩
    · exact ⟨w₀, fun h' => absurd h' h⟩
  choose wit hwit using hw
  let Q := Fintype.piFinset (fun _ : Fin 3 =>
    Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1))
  let f : ι → β × ℤ × κ × (Fin 3 → Fin 3 → ℤ) := fun s =>
    (blk s, frm s, wit s, fun m m' => cd s m m' - ref (wit s) (blk s) (frm s) m m')
  have hmaps : ∀ s ∈ S, f s ∈ Bs ×ˢ Ds ×ˢ Ws ×ˢ Q := by
    intro s hs
    obtain ⟨hb, hd, -⟩ := hS s hs
    obtain ⟨hwS, hc⟩ := hwit s hs
    simp only [Finset.mem_product, f, Q, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨hb, hd, hwS, fun m m' => ?_⟩
    exact abs_le.mp (hc m m')
  have hinjOn : Set.InjOn f S := by
    intro s hs s' hs' hf
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨hb, hd, hw', hc⟩ := hf
    apply hinj s hs s' hs' hb hd
    funext m m'
    have := congrFun (congrFun hc m) m'
    rw [hw', hb, hd] at this
    linarith
  calc S.card ≤ (Bs ×ˢ Ds ×ˢ Ws ×ˢ Q).card :=
        Finset.card_le_card_of_injOn f hmaps hinjOn
    _ = Bs.card * Ds.card * Ws.card * 3 ^ 9 := by
        rw [Finset.card_product, Finset.card_product, Finset.card_product, card_offsets]
        ring

/-! ## Frame windows -/

/-- The window of frames whose center is within `K q` of `z`. -/
def frameWindow (q z K : ℝ) : Finset ℤ :=
  Finset.Icc ⌈4 * z / q - 4 * K⌉ ⌊4 * z / q + 4 * K⌋

lemma mem_frameWindow {q z K : ℝ} (hq : 0 < q) {d : ℤ}
    (hd : |z - frameCenter q d| ≤ K * q) : d ∈ frameWindow q z K := by
  unfold frameWindow frameCenter at *
  rw [Finset.mem_Icc]
  rw [abs_le] at hd
  have h1 : 4 * z / q - 4 * K ≤ (d : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hq]
    nlinarith
  have h2 : (d : ℝ) ≤ 4 * z / q + 4 * K := by
    have h3 : (d : ℝ) ≤ (4 * z + 4 * K * q) / q := by rw [le_div_iff₀ hq]; nlinarith
    have e : (4 * z + 4 * K * q) / q = 4 * z / q + 4 * K := by field_simp
    linarith
  exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩

lemma card_frameWindow_le (q z K : ℝ) (hK : 0 ≤ K) :
    ((frameWindow q z K).card : ℝ) ≤ 8 * K + 1 := by
  unfold frameWindow
  rw [Int.card_Icc]
  have h1 := Int.floor_le (4 * z / q + 4 * K)
  have h2 := Int.le_ceil (4 * z / q - 4 * K)
  rcases le_or_gt (⌊4 * z / q + 4 * K⌋ + 1 - ⌈4 * z / q - 4 * K⌉) 0 with h | h
  · rw [Int.toNat_eq_zero.mpr h]
    simp only [Nat.cast_zero]
    linarith
  · have : ((⌊4 * z / q + 4 * K⌋ + 1 - ⌈4 * z / q - 4 * K⌉).toNat : ℝ) =
        ((⌊4 * z / q + 4 * K⌋ + 1 - ⌈4 * z / q - 4 * K⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h.le]
    rw [this]
    push_cast
    linarith

/-- The frame of an output label seen through a witness incidence: if the trajectory is within
`K q₁` of the label's frame center and within `M` of the witness line `u + t v` at a time of the
coarse block, the frame center is within `K q₁ + M + |v| q₁ / 2` of the witness center. -/
lemma frameCenter_near_witness {T₁ : ℕ} {b : Fin (2 ^ T₁)} {t : ℝ} (ht : t ∈ I T₁ b)
    {Y F u v K M : ℝ} (hF : |Y - F| ≤ K * width T₁) (hw : |Y - u - t * v| ≤ M) :
    |(u + mid T₁ b * v) - F| ≤ K * width T₁ + M + |v| * (width T₁ / 2) := by
  have hm := abs_sub_mid_le ht
  have hv : |v * (mid T₁ b - t)| ≤ |v| * (width T₁ / 2) := by
    rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_left hm (abs_nonneg v)
  calc |(u + mid T₁ b * v) - F| = |(Y - F) - (Y - u - t * v) + v * (mid T₁ b - t)| := by
        ring_nf
    _ ≤ |(Y - F) - (Y - u - t * v)| + |v * (mid T₁ b - t)| := abs_add_le _ _
    _ ≤ |Y - F| + |Y - u - t * v| + |v * (mid T₁ b - t)| := by
        linarith [abs_sub (Y - F) (Y - u - t * v)]
    _ ≤ K * width T₁ + M + |v| * (width T₁ / 2) := by linarith

/-! ## Blocks containing a time -/

lemma card_blocks_containing_le_two (T : ℕ) (t : ℝ) (s : Finset (Fin (2 ^ T)))
    (hs : ∀ b ∈ s, t ∈ I T b) : s.card ≤ 2 := by
  classical
  have hw := width_pos T
  let m : ℤ := ⌊t / width T⌋
  have hmaps : ∀ b ∈ s, ((b : ℕ) : ℤ) ∈ Finset.Icc (m - 1) m := by
    intro b hb
    have hb := hs b hb
    rw [I_eq] at hb
    have h1 : ((b : ℕ) : ℝ) ≤ t / width T := by rw [le_div_iff₀ hw]; exact hb.1
    have h2 : t / width T ≤ ((b : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hw]; exact hb.2
    rw [Finset.mem_Icc]
    constructor
    · have : t / width T < ((((b : ℕ) : ℤ) + 1 + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.floor_lt.mpr this
      omega
    · exact Int.le_floor.mpr (by exact_mod_cast h1)
  have hinj : Set.InjOn (fun b : Fin (2 ^ T) => ((b : ℕ) : ℤ)) s := by
    intro b _ b' _ h
    have h' : ((b : ℕ) : ℤ) = ((b' : ℕ) : ℤ) := h
    exact Fin.ext (by exact_mod_cast h')
  calc _ ≤ (Finset.Icc (m - 1) m).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 := by rw [Int.card_Icc]; omega

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
