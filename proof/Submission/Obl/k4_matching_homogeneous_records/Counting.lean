import Submission.Obl.k4_matching_homogeneous_records.Encoding

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

lemma finite_image_ncard_le_of_determines {α ι : Type*} [Fintype ι]
    (S : Set α) (F : α → ℕ) (g : S → ι)
    (hd : ∀ x y : S, g x = g y → F x = F y) :
    (F '' S).Finite ∧ (F '' S).ncard ≤ Fintype.card ι := by
  classical
  let φ : ι → ℕ := fun i => if hi : ∃ x : S, g x = i then F hi.choose else 0
  have hφ (x : S) : φ (g x) = F x := by
    dsimp [φ]
    split_ifs with hi
    · exact hd hi.choose x hi.choose_spec
    · exact (hi ⟨x, rfl⟩).elim
  have hsub : F '' S ⊆ range φ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨g ⟨x, hx⟩, hφ ⟨x, hx⟩⟩
  have hf := finite_range φ
  refine ⟨hf.subset hsub, (ncard_le_ncard hsub hf).trans ?_⟩
  simpa [image_univ] using (ncard_image_le (s := (univ : Set ι)) (f := φ))

noncomputable def jetOffset {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (v j : ℕ)
    (p : (Fin n₁ × Fin n₂) × ℝ) : ℤ :=
  Int.floor (w v j * iteratedDeriv j (f₂ p.1.2) (dyadicCenter (h v) p.2)) -
    Int.floor (w v j * iteratedDeriv j (f₁ p.1.1) (dyadicCenter (h v) p.2))

lemma floor_dyadic_mem {h : ℕ} {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Int.floor (t * (2 : ℝ) ^ h) ∈ Finset.Ico (0 : ℤ) ((2 : ℤ) ^ h) := by
  rw [Finset.mem_Ico]
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg ht.1 (by positivity))
  · apply Int.floor_lt.mpr
    push_cast
    nlinarith [show (0 : ℝ) < 2 ^ h by positivity, ht.2]

lemma offset_card (K : ℕ) :
    Fintype.card {z : ℤ // z ∈ Finset.Icc (-(K : ℤ)) K} = 2 * K + 1 := by
  simp only [Fintype.card_coe, Int.card_Icc]
  omega

lemma time_card (h : ℕ) :
    Fintype.card {z : ℤ // z ∈ Finset.Ico (0 : ℤ) ((2 : ℤ) ^ h)} = 2 ^ h := by
  simp only [Fintype.card_coe, Int.card_Ico, sub_zero]
  norm_cast

lemma recordCode_count {n₁ n₂ : ℕ} (q J K : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (hS : ∀ p ∈ S, p.2 ∈ Ico (0 : ℝ) 1)
    (hh : ∀ v, v ≤ q → h v ≤ h q)
    (hoff : ∀ p ∈ S, ∀ v, v ≤ q → ∀ j, j ≤ J →
      jetOffset f₁ f₂ h w v j p ∈ Finset.Icc (-(K : ℤ)) K) :
    (∀ k, k ≤ q → (recordCode q J f₁ f₂ h w k '' S).Finite) ∧
    (recordCode q J f₁ f₂ h w q '' S).ncard ≤
      n₁ * 2 ^ h q * (2 * K + 1) ^ ((q + 1) * (J + 1)) := by
  classical
  let P := Fin n₁ × ({z : ℤ // z ∈ Finset.Ico (0 : ℤ) ((2 : ℤ) ^ h q)} ×
    (Fin (q + 1) → Fin (J + 1) → {z : ℤ // z ∈ Finset.Icc (-(K : ℤ)) K}))
  let g : S → P := fun p =>
    (p.val.1.1, (⟨Int.floor (p.val.2 * (2 : ℝ) ^ h q), floor_dyadic_mem (hS p p.property)⟩,
      fun v j => ⟨jetOffset f₁ f₂ h w v j p, hoff p p.property v (by omega) j (by omega)⟩))
  have hdet (x y : S) (he : g x = g y) :
      recordCode q J f₁ f₂ h w q x = recordCode q J f₁ f₂ h w q y := by
    have hi : x.val.1.1 = y.val.1.1 := congrArg (fun p : P => p.1) he
    have ht : Int.floor (x.val.2 * (2 : ℝ) ^ h q) =
        Int.floor (y.val.2 * (2 : ℝ) ^ h q) :=
      congrArg (fun p : P => p.2.1.val) he
    apply (recordCode_eq_iff q J f₁ f₂ h w le_rfl x y).2
    intro v hv
    have htv := floor_dyadic_eq_of_finer_eq (hh v hv) ht
    have hc : dyadicCenter (h v) x.val.2 = dyadicCenter (h v) y.val.2 := by
      simp only [dyadicCenter, htv]
    refine ⟨htv, ?_⟩
    intro j hj
    have ho : jetOffset f₁ f₂ h w v j x = jetOffset f₁ f₂ h w v j y :=
      congrArg (fun p : P => (p.2.2 (⟨v, by omega⟩ : Fin (q + 1))
        (⟨j, by omega⟩ : Fin (J + 1))).val) he
    have h1 : Int.floor (w v j * iteratedDeriv j (f₁ x.val.1.1) (dyadicCenter (h v) x.val.2)) =
        Int.floor (w v j * iteratedDeriv j (f₁ y.val.1.1) (dyadicCenter (h v) y.val.2)) := by
      rw [hi, hc]
    refine ⟨h1, ?_⟩
    dsimp [jetOffset] at ho
    omega
  have hdetk (k : ℕ) (hk : k ≤ q) (x y : S) (he : g x = g y) :
      recordCode q J f₁ f₂ h w k x = recordCode q J f₁ f₂ h w k y :=
    recordCode_nested q J f₁ f₂ h w hk le_rfl x y (hdet x y he)
  have hcard : Fintype.card P = n₁ * 2 ^ h q * (2 * K + 1) ^ ((q + 1) * (J + 1)) := by
    simp only [P, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, time_card, offset_card]
    rw [← pow_mul]
    ring
  refine ⟨fun k hk => (finite_image_ncard_le_of_determines S _ g (hdetk k hk)).1, ?_⟩
  simpa only [hcard] using (finite_image_ncard_le_of_determines S _ g hdet).2

end Submission.Obl.k4_matching_homogeneous_records
