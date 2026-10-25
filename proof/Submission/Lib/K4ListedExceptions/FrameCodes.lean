import Mathlib

/-!
Adapted from: here:o114 (session x0383).

Finite-code counting for x0524's 2026-10-21 07:05Z common-frame construction.
The four center/velocity coordinates may depend on the normal code. Clipping
this neighborhood to the actually used frame codes preserves its local count.

This generalizes the fixed-radius cube counting in accepted o175 Bins.lean;
all proofs here use Mathlib's finite products and integer floors directly.
-/

namespace Submission.Lib.K4ListedExceptions

open Finset

noncomputable def integerCodeBox {n : ℕ} (C : ℕ) (q : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun i => Icc (q i - C) (q i + C))

theorem card_integerCodeBox {n : ℕ} (C : ℕ) (q : Fin n → ℤ) :
    (integerCodeBox C q).card = (2*C+1)^n := by
  have h (i : Fin n) : (Icc (q i - C) (q i + C)).card = 2*C+1 := by
    rw [Int.card_Icc]
    omega
  simp [integerCodeBox, h]

theorem mem_integerCodeBox {n : ℕ} (C : ℕ) (q z : Fin n → ℤ) :
    z ∈ integerCodeBox C q ↔ ∀ i, q i - C ≤ z i ∧ z i ≤ q i + C := by
  simp [integerCodeBox]

/-- Coordinate errors of at most C grid widths give an integer C-neighborhood. -/
theorem floor_code_mem_integerCodeBox {n : ℕ} (C : ℕ) (u v s : Fin n → ℝ)
    (hs : ∀ i, 0 < s i) (hclose : ∀ i, |u i - v i| ≤ (C : ℝ) * s i) :
    (fun i => ⌊u i / s i⌋) ∈ integerCodeBox C (fun i => ⌊v i / s i⌋) := by
  rw [mem_integerCodeBox]
  intro i
  have hdiv : |u i / s i - v i / s i| ≤ (C : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos (hs i)]
    exact (div_le_iff₀ (hs i)).mpr (hclose i)
  have hlo : v i / s i - (C : ℝ) ≤ u i / s i := by
    linarith [(abs_le.mp hdiv).1]
  have hhi : u i / s i ≤ v i / s i + (C : ℝ) := by
    linarith [(abs_le.mp hdiv).2]
  exact ⟨by simpa using Int.floor_mono hlo, by simpa using Int.floor_mono hhi⟩

abbrev FrameCode := (Fin 2 → ℤ) × (Fin 4 → ℤ)

/-- Both signs of a witness normal are allowed. -/
noncomputable def normalCodeNeighbors (C : ℕ) (qpos qneg : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) := integerCodeBox C qpos ∪ integerCodeBox C qneg

theorem card_normalCodeNeighbors_le (C : ℕ) (qpos qneg : Fin 2 → ℤ) :
    (normalCodeNeighbors C qpos qneg).card ≤ 2*(2*C+1)^2 := by
  exact (card_union_le _ _).trans (by rw [card_integerCodeBox, card_integerCodeBox]; omega)

/-- For each candidate normal, use that normal's own predicted center/velocity
code. No global range of grid coordinates is required. -/
noncomputable def frameCodeNeighbors (C : ℕ) (qpos qneg : Fin 2 → ℤ)
    (center : (Fin 2 → ℤ) → Fin 4 → ℤ) : Finset FrameCode :=
  (normalCodeNeighbors C qpos qneg).biUnion fun q =>
    (integerCodeBox C (center q)).image (fun r => (q,r))

theorem mem_frameCodeNeighbors (C : ℕ) (qpos qneg : Fin 2 → ℤ)
    (center : (Fin 2 → ℤ) → Fin 4 → ℤ) (q : Fin 2 → ℤ) (r : Fin 4 → ℤ) :
    (q,r) ∈ frameCodeNeighbors C qpos qneg center ↔
      q ∈ normalCodeNeighbors C qpos qneg ∧ r ∈ integerCodeBox C (center q) := by
  simp [frameCodeNeighbors]

theorem card_frameCodeNeighbors_le (C : ℕ) (qpos qneg : Fin 2 → ℤ)
    (center : (Fin 2 → ℤ) → Fin 4 → ℤ) :
    (frameCodeNeighbors C qpos qneg center).card ≤ 2*(2*C+1)^6 := by
  have hcard (q : Fin 2 → ℤ) :
      ((integerCodeBox C (center q)).image (fun r => (q,r))).card = (2*C+1)^4 := by
    rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), card_integerCodeBox]
  calc
    (frameCodeNeighbors C qpos qneg center).card ≤
        ∑ q ∈ normalCodeNeighbors C qpos qneg,
          ((integerCodeBox C (center q)).image (fun r => (q,r))).card := card_biUnion_le
    _ = (normalCodeNeighbors C qpos qneg).card * (2*C+1)^4 := by simp only [hcard, sum_const_nat]
    _ ≤ (2*(2*C+1)^2) * (2*C+1)^4 :=
      Nat.mul_le_mul_right _ (card_normalCodeNeighbors_le C qpos qneg)
    _ = 2*(2*C+1)^6 := by ring

/-- Restricting to the finite image of the old source labels costs no extra
compatibility labels. -/
theorem card_used_frameCodeNeighbors_le (used : Finset FrameCode) (C : ℕ)
    (qpos qneg : Fin 2 → ℤ) (center : (Fin 2 → ℤ) → Fin 4 → ℤ) :
    (used ∩ frameCodeNeighbors C qpos qneg center).card ≤ 2*(2*C+1)^6 :=
  (card_le_card inter_subset_right).trans (card_frameCodeNeighbors_le C qpos qneg center)

/-- Any injective finite enumeration of frame codes inherits the code count. -/
theorem card_enumerated_frameCodeNeighbors_le {α : Type*} [Fintype α]
    (code : α → FrameCode) (hinj : Function.Injective code) (C : ℕ)
    (qpos qneg : Fin 2 → ℤ) (center : (Fin 2 → ℤ) → Fin 4 → ℤ) :
    ((univ.filter fun a => code a ∈ frameCodeNeighbors C qpos qneg center).card) ≤
      2*(2*C+1)^6 := by
  classical
  let A := univ.filter fun a => code a ∈ frameCodeNeighbors C qpos qneg center
  have hsub : A.image code ⊆ frameCodeNeighbors C qpos qneg center := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp ha).2
  calc
    A.card = (A.image code).card := (card_image_of_injective _ hinj).symm
    _ ≤ (frameCodeNeighbors C qpos qneg center).card := card_le_card hsub
    _ ≤ _ := card_frameCodeNeighbors_le C qpos qneg center

/-- The finite used-code image has no more entries than the old label family. -/
theorem card_used_frame_codes_le {α : Type*} [Fintype α] (code : α → FrameCode) :
    (univ.image code).card ≤ Fintype.card α := by
  exact (card_image_le).trans_eq card_univ

/-- A real-valued geometric margin gives a polynomial local list bound. -/
theorem card_frameCodeNeighbors_real_le (R : ℝ) (hR : 0 ≤ R)
    (qpos qneg : Fin 2 → ℤ) (center : (Fin 2 → ℤ) → Fin 4 → ℤ) :
    ((frameCodeNeighbors ⌈R⌉₊ qpos qneg center).card : ℝ) ≤ 2*(2*R+3)^6 := by
  have hcount : ((frameCodeNeighbors ⌈R⌉₊ qpos qneg center).card : ℝ) ≤
      2*(2*(⌈R⌉₊ : ℝ)+1)^6 := by exact_mod_cast card_frameCodeNeighbors_le ⌈R⌉₊ qpos qneg center
  have hceil : (⌈R⌉₊ : ℝ) < R+1 := Nat.ceil_lt_add_one hR
  calc
    _ ≤ 2*(2*(⌈R⌉₊ : ℝ)+1)^6 := hcount
    _ ≤ 2*(2*R+3)^6 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 6

/-- In particular, a margin proportional to the old subpower parameter only
costs a fixed sixth power of that parameter. -/
theorem card_frameCodeNeighbors_poly_le (A K : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    (qpos qneg : Fin 2 → ℤ) (center : (Fin 2 → ℤ) → Fin 4 → ℤ) :
    ((frameCodeNeighbors ⌈A*K⌉₊ qpos qneg center).card : ℝ) ≤
      (2*(2*A+3)^6) * K^6 := by
  have hAK : 0 ≤ A*K := mul_nonneg hA (zero_le_one.trans hK)
  calc
    _ ≤ 2*(2*(A*K)+3)^6 := card_frameCodeNeighbors_real_le (A*K) hAK qpos qneg center
    _ ≤ 2*((2*A+3)*K)^6 := by gcongr <;> nlinarith
    _ = _ := by rw [mul_pow]; ring

end Submission.Lib.K4ListedExceptions
